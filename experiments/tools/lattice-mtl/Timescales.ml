open LatticeMtl;;

let buff = [| 0.3954132773952119 ; 0.7802043456276684 ; 0.9056838067459964 ;
                 0.9919627616090054 ; 0.3153684746871873 ; 0.868398327264566 ;
                 0.8470972988532026 ; 0.7257287331532113 ; 0.8272851976726383 ;
                 0.15529920818726972 ;
              |]

let test1 = (fun x -> x -. 0.50)
let test2 = (fun x -> x -. 0.00)
let test3 = (fun x -> x -. 0.25)
let test4 = (fun x -> x -. 0.75)
let ntest1 = (fun x -> 0.50 -. x)
let ntest2 = (fun x -> 0.00 -. x)
let ntest3 = (fun x -> 0.25 -. x)
let ntest4 = (fun x -> 0.75 -. x)

let realL = {join = (max); meet = (min); }
let realLB = {top = infinity; bottom = neg_infinity; }

let fAtomic1 = FAtomic test1
let fAtomic2 = FAtomic test2
let fAtomic3 = FAtomic test3
let fAtomic4 = FAtomic test4
let negfAtomic1 = FAtomic ntest1
let negfAtomic2 = FAtomic ntest2
let negfAtomic3 = FAtomic ntest3
let negfAtomic4 = FAtomic ntest4

let tsform0 b = FOr (FSometime(0, b, negfAtomic2), FSinceUnbounded(0, negfAtomic1, fAtomic2))
let tsform1 b = FOr (negfAtomic3, FAlways(0, b, negfAtomic1))
let tsform2 b = FOr (FOr (FOr (negfAtomic3, fAtomic2), FAlwaysUnbounded(0, negfAtomic2)), FSince(b, 2*b, negfAtomic1, fAtomic2))
let tsform3 b = FOr (FAlways(0, b, negfAtomic2), FSinceUnbounded(0, fAtomic1, fAtomic2))
let tsform4 b = FOr (negfAtomic3, FAlways(0, b, fAtomic1))

let tsform5 b = FOr ( FOr (FOr(negfAtomic3, fAtomic2), FAlwaysUnbounded(0, negfAtomic2)), FSince(1000, 2000, fAtomic1, fAtomic2))
let tsform6 b = FSometime(0, b, fAtomic1)
let tsform7 b = FOr (FOr (FOr(negfAtomic3, fAtomic2), FAlwaysUnbounded(0, negfAtomic2)), FSometime(0, b, FSinceUnbounded(0, FOr(fAtomic1, fAtomic2), fAtomic2)))
let tsform8 b = FAnd (
	FOr(negfAtomic4, FSometime(b, 2*b, fAtomic1)) ,
	FSinceDualUnbounded (b, fAtomic4, negfAtomic1)
	 )
let tsform9 b = FOr (
	FOr (FOr(negfAtomic3, fAtomic2), FAlwaysUnbounded(0, negfAtomic2)),
	FAnd (
	 FOr(negfAtomic4, FSometime(b, 2*b, fAtomic1)) ,
	 FSinceDualUnbounded (1000, fAtomic4, negfAtomic1)
	))

let forms = [tsform0; tsform1; tsform2; tsform3; tsform4;
             tsform5; tsform6; tsform7; tsform8; tsform9]

let describer f bound = "F"^(string_of_int f) ^ "(" ^ (string_of_int bound) ^ ")"

let measure form strmlen desc =
  print_endline "Tool=lattice-monitor";
  print_endline ("Formula="^desc);
  print_endline ("StremLength="^ (string_of_int strmlen));
  let monbox = ref (toMonitor realL realLB form) in
  let cntbox = ref 0 in
  let thenn = Unix.gettimeofday () in
  for i = 0 to strmlen-1 do
      let inp = (Array.get buff (i mod 10)) in
      if ((mOut !monbox inp) > 0.0)
      then begin cntbox := !cntbox + 1; end
      else ();
      monbox := mNext (!monbox) inp;
  done;
  let now = Unix.gettimeofday () in
  print_endline ("TimeUnit = ms");
  print_endline ("TimeElapsed = " ^ string_of_float ((now -. thenn) *. 1000.0));
  print_endline (string_of_int !cntbox)

let formarg = ref 0
let bound = ref 0
let streamSize = ref 0

let speclist = [
      ("-f", Arg.Set_int formarg, ": set formula");
      ("-b", Arg.Set_int bound, ": set bound");
      ("-l", Arg.Set_int streamSize, ": set streamSize");
    ]

let suite () =
        measure ((List.nth forms !formarg) !bound) (!streamSize) (describer !formarg !bound)

let main =
    Arg.parse
     speclist
     (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
     "-f [0-9] -b [bound] -l [strmlen]";
    suite ()
