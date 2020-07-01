(**
To run this file:

rm *.mli *.o *.cmx *.cmi
ocamlopt -o a.out unix.cmxa Extracted.ml Experiments.ml
./a.out

**)

open Extracted;;

(* This generates the signal *)

type signal = { x : float; y : float; z : float; }

let test1 = (fun sg -> sg.x -. 0.50)
let test2 = (fun sg -> sg.y -. 0.25)

let buffbox = ref (Array.init 1000 (fun _ -> {x = Random.float 1.0; y = Random.float 1.0; z = Random.float 1.0;} ))

(* This is the main mechanism for measuring and printing the results *)
let measure strmlen form descr =
	print_endline("-------------------------------------------");
	let monbox = ref (toMonitor form) in
  print_endline "tool = Our Tool";
	print_endline descr;
	Printf.printf "stream length = %#n\n" strmlen;
	let startTs: float = Sys.time() in
	for i = 0 to strmlen-1 do
		(mOut !monbox);
   	monbox := mNext (!monbox) (Array.get !buffbox (i mod 1000));
	done;
	let endTs: float = Sys.time() in
	let duration: float = endTs -. startTs in
	print_endline ("duration = " ^ (string_of_float duration) ^ " sec");
	let throughput: int = truncate ((float_of_int strmlen) /. duration) in
	print_endline ("throughput = " ^ (string_of_int throughput) ^ " items/sec")

let form1 = FAtomic test1
let form2 = FAtomic test2
let form3 = FAnd (form1, form2)
let form4 = FOr (form1, form2)
let form5 = FSometime form1
let form6 = FAlways form1
let form7 = FSince (form1, form2)
let form8 = FSinceDual (form1, form2)
let form9 = FDelayDual(10, form1)
let form10 = FDelay(10, form1)
let form11 = FDelay(100, form1)
let form12 = FDelay(1000, form1)
let form13 = FDelay(10000, form1)
let form14 = FDelay(100000, form1)
let form15 = FDelay(1000000, form1)
let form16 = FAlwaysWithin(10, form1)
let form17 = FSometimeWithin(10, form1)
let form18 = FSometimeWithin(100, form1)
let form19 = FSometimeWithin(1000, form1)
let form20 = FSometimeWithin(10000, form1)
let form21 = FSometimeWithin(100000, form1)
let form22 = FSometimeWithin(1000000, form1)
let form23 = fSinceAfter 1000 form1 form2
let form24 = fSinceBounded 1000 2000 form1 form2
let form25 = fPre form1
let form26 = fSinceWithin 10 form1 form2
let form27 = fSinceWithin 100 form1 form2
let form28 = fSinceWithin 1000 form1 form2
let form29 = fSinceWithin 10000 form1 form2
let form30 = fSinceWithin 100000 form1 form2

let suite () =
               buffbox := Array.init 1000 (fun _ -> {x = Random.float 1.0; y = Random.float 1.0; z = Random.float 1.0;});
               measure 200_000_000 form1 "{x > 0.5}";
  						 measure 200_000_000 form2 "{x > 0.25}";
  						 measure 200_000_000 form3 "{x > 0.5} and {x > 0.25}";
  						 measure 200_000_000 form4 "{x > 0.5} or {x > 0.25}";
  						 measure 200_000_000 form5 "once {x > 0.5}";
  						 measure 200_000_000 form6 "historically {x > 0.5}";
  						 measure 200_000_000 form7 "{x > 0.5} since {x > 0.25}";
  						 measure 200_000_000 form8  "not ({x <= 0.5} since {x <= 0.25})";
  						 measure 200_000_000 form9  "historically [10:10] {x > 0.5}";
  						 measure 200_000_000 form10 "once [10:10] {x > 0.5}";
  						 measure 200_000_000 form11 "once [100:100] {x > 0.5}";
  						 measure 200_000_000 form12 "once [1000:1000] {x > 0.5}";
  						 measure 200_000_000 form13 "once [10000:10000] {x > 0.5}";
  						 measure 200_000_000 form14 "once [100000:100000] {x > 0.5}";
  						 measure 200_000_000 form15 "once [1000000:1000000] {x > 0.5}";
  						 measure 200_000_000 form16 "historically[:10] {x > 0.5}";
  						 measure 200_000_000 form17 "once[:10] {x > 0.5}";
  						 measure 200_000_000 form18 "once[:100] {x > 0.5}";
  						 measure 200_000_000 form19 "once[:1000] {x > 0.5}";
  						 measure 200_000_000 form20 "once[:10000] {x > 0.5}";
  					 	 measure 200_000_000 form21 "once[:100000] {x > 0.5}";
  					   measure 200_000_000 form22 "once[:1000000] {x > 0.5}";
  					   measure 200_000_000 form23 "{x > 0.5} since[1000:] {x > 0.25}";
  					 	 measure 200_000_000 form24 "{x > 0.5} since[1000:2000] {x > 0.25}";
  						 measure 200_000_000 form25 "previously {x > 0.5}";
               measure 200_000_000 form26 "{x > 0.5} since[:10] {x > 0.25}";
               measure 200_000_000 form27 "{x > 0.5} since[:100] {x > 0.25}";
               measure 200_000_000 form28 "{x > 0.5} since[:1000] {x > 0.25}";
               measure 200_000_000 form29 "{x > 0.5} since[:10000] {x > 0.25}";
               measure 200_000_000 form30 "{x > 0.5} since[:100000] {x > 0.25}"

let main =
  print_endline ("timestamp = " ^ (string_of_float (Unix.time ())) ^ " seconds after epoch");
  for i = 1 to 10 do
    suite ();
  done
