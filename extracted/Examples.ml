
(**
To run this file:
rm *.mli *.o *.cmx *.cmi
ocamlopt -o a.out unix.cmxa LatticeMtl.ml Examples.ml
./a.out
**)

open LatticeMtl;;

type signal = { x : float; y : float; z : float; }

(** Real Numbers with min/max **)
let realL = {join = (max); meet = (min); }
let realLB = {top = infinity; bottom = neg_infinity; }

let real1 = (fun sg -> sg.x -. 0.50)
let real2 = (fun sg -> sg.y -. 0.25)

let fReal1 = FAtomic real1
let fReal2 = FAtomic real2
let fReal3 = FSince(2,5, fReal1, fReal2)

let mReal3 = toMonitor realL realLB fReal3

(** Booleans **)

let boolL = {join = (||); meet = (&&); }
let boolLB = {top = true; bottom = false; }

let bool1 = (fun sg -> sg.x > 0.50)
let bool2 = (fun sg -> sg.y > 0.25)

let fBool1 = FAtomic bool1
let fBool2 = FAtomic bool2
let fBool3 = FSince(2,5, fBool1, fBool2)

let mBool3 = toMonitor boolL boolLB fBool3

(** Running the Monitors **)

let buffbox = ref (Array.init 5 (fun _ -> {x = Random.float 1.0; y = Random.float 1.0; z = Random.float 1.0;} ))

let run mon =
  let monBox = ref mon in
  for i = 0 to 19 do
    let inp = Array.get !buffbox (i mod 5) in
    (mOut !monBox inp);
    monBox := mNext !monBox inp;
  done

let main = run mReal3; run mBool3
