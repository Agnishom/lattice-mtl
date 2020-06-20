(**
To run this file:

ocamlopt -c Extracted.ml
ocamlopt -c Tests.ml
ocamlopt -o a.out Extracted.cmx Tests.cmx
./a.out

**)

open Extracted;;

type signal = { x : float; y : float; z : float; }

let test1 = (fun sg -> sg.x -. 0.50)
let test2 = (fun sg -> sg.y -. 0.25)

let buff = Array.init 1000 (fun _ -> {x = Random.float 1.0; y = Random.float 1.0; z = Random.float 1.0;} )

let n = 200_000_000

let measure form descr =
	print_endline("-------------------------------------------");
	let monbox = ref (toMonitor form) in
	print_endline descr;
	Printf.printf "stream length = %#n\n" n;
	let startTs: float = Sys.time() in
	for i = 0 to n-1 do
		(mOut !monbox);
   		monbox := mNext (!monbox) (Array.get buff (i mod 1000));
	done;
	let endTs: float = Sys.time() in
	let duration: float = endTs -. startTs in
	print_endline ("duration = " ^ (string_of_float duration) ^ " sec");
	let throughput: int = truncate ((float_of_int n) /. duration) in
	print_endline ("throughput = " ^ (string_of_int throughput) ^ " items/sec")

let form1 = FAtomic test1
let form2 = FAtomic test2
let form3 = FAnd (form1, form2)
let form4 = FOr (form1, form2)
let form5 = FSometime form1
let form6 = FAlways form1
let form7 = FSince (form1, form2)
let form8 = fPre form1
let form9 = FDelay(10, form1)
let form10 = FDelay(20, form1)
let form11 = FAlwaysWithin(10, form1)
let form12 = FSometimeWithin(10, form1)
let form13 = FSometimeWithin(20, form1)
let form14 = FSometimeWithin(40, form1)
let form15 = fSometimeBounded 10 20 form1
let form16 = fSometimeBounded 10 30 form1
let form17 = fSometimeBounded 20 60 form1
let form18 = fSinceAfter 10  form1 form2
let form19 = fSinceAfter 20 form1 form2
let form20 = fSinceAfter 40 form1 form2
let form21 = FSinceWithin(5,form1, form2)
let form22 = FSinceWithin(10,form1, form2)
let form23 = FSinceWithin(15,form1, form2)
let form24 = fSinceBounded 1 5 form1 form2
let form25 = fSinceBounded 5 10 form1 form2
let form26 = fSinceBounded 15 20 form1 form2



let main =  measure form1 "FAtomic test1";
						measure form2 "FAtomic test2";
						measure form3 "FAnd (form1, form2)";
						measure form4 "FOr (form1, form2)";
						measure form5 "FSometime form1";
						measure form6 "FAlways form1";
						measure form7 "FSince (form1, form2)";
						measure form8 "fPre form1";
						measure form9 "FDelay(10, form1)";
						measure form10 "FDelay(20, form1)";
						measure form11 "FAlwaysWithin(10, form1)";
						measure form12 "FSometimeWithin(10, form1)";
						measure form13 "FSometimeWithin(20, form1)";
						measure form14 "FSometimeWithin(40, form1)";
						measure form15 "fSometimeBounded 10 20 form1";
						measure form16 "fSometimeBounded 10 30 form1";
						measure form17 "fSometimeBounded 20 60 form1";
						measure form18 "fSinceAfter 10 form1 form2";
						measure form19 "fSinceAfter 20 form1 form2";
						measure form20 "fSinceAfter 40 form1 form2";
						measure form21 "FSinceWithin(5, form1, form2)";
						measure form22 "FSinceWithin(10, form1, form2)";
						measure form23 "FSinceWithin(15, form1, form2)";
						measure form24 "fSinceBounded 1 5 form1 form2";
						measure form25 "fSinceBounded 5 10 form1 form2";
						measure form26 "fSinceBounded 15 20 form1 form2";


(**
-------------------------------------------
FAtomic test1
stream length = 200000000
duration = 3.026455 sec
throughput = 66083916 items/sec
-------------------------------------------
FAtomic test2
stream length = 200000000
duration = 3.021647 sec
throughput = 66189068 items/sec
-------------------------------------------
FAnd (form1, form2)
stream length = 200000000
duration = 11.814427 sec
throughput = 16928455 items/sec
-------------------------------------------
FOr (form1, form2)
stream length = 200000000
duration = 11.837278 sec
throughput = 16895776 items/sec
-------------------------------------------
FSometime form1
stream length = 200000000
duration = 10.698625 sec
throughput = 18693991 items/sec
-------------------------------------------
FAlways form1
stream length = 200000000
duration = 10.656481 sec
throughput = 18767921 items/sec
-------------------------------------------
FSince (form1, form2)
stream length = 200000000
duration = 19.342356 sec
throughput = 10340002 items/sec
-------------------------------------------
fPre form1
stream length = 200000000
duration = 6.230839 sec
throughput = 32098406 items/sec
-------------------------------------------
FDelay(10, form1)
stream length = 200000000
duration = 6.335263 sec
throughput = 31569328 items/sec
-------------------------------------------
FDelay(20, form1)
stream length = 200000000
duration = 6.313706 sec
throughput = 31677116 items/sec
-------------------------------------------
FAlwaysWithin(10, form1)
stream length = 200000000
duration = 18.580891 sec
throughput = 10763746 items/sec
-------------------------------------------
FSometimeWithin(10, form1)
stream length = 200000000
duration = 18.6148 sec
throughput = 10744139 items/sec
-------------------------------------------
FSometimeWithin(20, form1)
stream length = 200000000
duration = 18.117702 sec
throughput = 11038927 items/sec
-------------------------------------------
FSometimeWithin(40, form1)
stream length = 200000000
duration = 17.78082 sec
throughput = 11248075 items/sec
-------------------------------------------
fSometimeBounded 10 20 form1
stream length = 200000000
duration = 22.065451 sec
throughput = 9063943 items/sec
-------------------------------------------
fSometimeBounded 10 30 form1
stream length = 200000000
duration = 21.634307 sec
throughput = 9244576 items/sec
-------------------------------------------
fSometimeBounded 20 60 form1
stream length = 200000000
duration = 21.355286 sec
throughput = 9365362 items/sec
-------------------------------------------
fSinceAfter 10  form1 form2
stream length = 200000000
duration = 22.888954 sec
throughput = 8737839 items/sec
-------------------------------------------
fSinceAfter 20 form1 form2
stream length = 200000000
duration = 22.894784 sec
throughput = 8735614 items/sec
-------------------------------------------
fSinceAfter 40 form1 form2
stream length = 200000000
duration = 23.059849 sec
throughput = 8673083 items/sec
-------------------------------------------
FSinceWithin(5,form1, form2)
stream length = 200000000
duration = 296.216302 sec
throughput = 675182 items/sec
-------------------------------------------
FSinceWithin(10,form1, form2)
stream length = 200000000
duration = 1155.846525 sec
throughput = 173033 items/sec
-------------------------------------------
FSinceWithin(15,form1, form2)
stream length = 200000000
duration = 2846.886804 sec
throughput = 70252 items/sec
-------------------------------------------
fSinceBounded 1 5 form1 form2
stream length = 200000000
duration = 235.290103 sec
throughput = 850014 items/sec
-------------------------------------------
fSinceBounded 5 10 form1 form2
stream length = 200000000
duration = 325.10844 sec
throughput = 615179 items/sec
-------------------------------------------
fSinceBounded 15 20 form1 form2
stream length = 200000000
duration = 325.923862 sec
throughput = 613640 items/sec
**)
