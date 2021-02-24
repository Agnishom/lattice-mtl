open LatticeMtl;;

let buff = [| 0.3954132773952119 ; 0.7802043456276684 ; 0.9056838067459964 ;
                 0.9919627616090054 ; 0.3153684746871873 ; 0.868398327264566 ;
                 0.8470972988532026 ; 0.7257287331532113 ; 0.8272851976726383 ;
                 0.15529920818726972 ;
              |]

let test1 = (fun x -> x -. 0.50)
let test2 = (fun x -> x -. 0.00)

let realL = {join = (max); meet = (min); }
let realLB = {top = infinity; bottom = neg_infinity; }

let fAtomic1 = FAtomic test1
let fAtomic2 = FAtomic test2

let sometime_up b = FSometime(0, b, fAtomic1)
let sometime_at b = fDelay b fAtomic1
let sometime_lo_up b = FSometime(b, 2*b, fAtomic1)
let sometime_lo b = FSometimeUnbounded(b, fAtomic1)

let since_up b = FSince(0, b, fAtomic1, fAtomic2)
let since_at b = FSince(b, b, fAtomic1, fAtomic2)
let since_lo_up b = FSince(b, 2*b, fAtomic1, fAtomic2)
let since_lo b = FSinceUnbounded(b, fAtomic1, fAtomic2)

let forms = [sometime_up; sometime_at; sometime_lo_up; sometime_lo;
            since_up; since_at; since_lo_up; since_lo]

let describer f bound =
  if (f == 0)
  then "once[0:" ^ string_of_int(bound) ^ "] x > 0.5"
  else if (f == 1)
  then "once[" ^ string_of_int(bound) ^ ":" ^ string_of_int(bound) ^ "] x > 0.5"
  else if (f == 2)
  then "once[" ^ string_of_int(bound) ^ ":" ^ string_of_int(2*bound) ^ "] x > 0.5"
  else if (f == 3)
  then "once[" ^ string_of_int(bound) ^ ":] x > 0.5"
  else if (f == 4)
  then "x > 0 since[0:" ^ string_of_int(bound) ^ "] x > 0.5"
  else if (f == 5)
  then "x > 0 since[" ^ string_of_int(bound) ^ ":" ^ string_of_int(bound) ^ "] x > 0.5"
  else if (f == 6)
  then "x > 0 since[" ^ string_of_int(bound) ^ ":" ^ string_of_int(2*bound) ^ "] x > 0.5"
  else if (f == 7)
  then "x > 0 since[" ^ string_of_int(bound) ^ ":] x > 0.5"
  else "wrong formula argument"

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
  print_endline ("TimeUnit=ms");
  print_endline ("TimeElapsed=" ^ string_of_float ((now -. thenn) *. 1000.0));
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
     "-f [0-7] -b [bound] -l [strmlen]";
    suite ()
