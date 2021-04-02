open LatticeMtl;;

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

let interact form =
  let monbox = ref (toMonitor realL realLB form) in
  let quit_loop = ref false in
  while not !quit_loop do
      let inl = read_line () in
      if inl = "DONE"
      then quit_loop := true
      else
        let inp = Float.of_string inl in
        Printf.printf "%.17g" (mOut !monbox inp);
        print_newline ();
        monbox := mNext (!monbox) inp
  done

let formarg = ref 0
let bound = ref 0

let speclist = [
      ("-f", Arg.Set_int formarg, ": set formula");
      ("-b", Arg.Set_int bound, ": set bound");
    ]

let suite () =
        interact ((List.nth forms !formarg) !bound)

let main =
    Arg.parse
     speclist
     (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
     "-f [0-7] -b [bound]";
    suite ()
