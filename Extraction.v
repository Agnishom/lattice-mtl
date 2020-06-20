Require Import Monitor.
Require Import Lattice.
Require Import Formula.

Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlNatInt.
Extraction Language Ocaml.

(* Boolean Monitor *)
Extract Constant Monitor.Val => bool.
Extract Constant Monitor.lattice_val => "{join = (||); meet = (&&); }".
Extract Constant Monitor.boundedLattice_val => "{top = true; bottom = false; }".

Extraction "extracted/ExtractedBool.ml"
           toMonitor FPre FSometimeBounded FAlwaysBounded
           FSinceWithin FSinceBounded FSinceAfter
           FSinceWithinDual FSinceBoundedDual FSinceAfterDual.

(* Floating Monitor *)

Extract Constant Monitor.Val => float.
Extract Constant Monitor.lattice_val => "{join = (max); meet = (min); }".
Extract Constant Monitor.boundedLattice_val => "{top = infinity; bottom = neg_infinity; }".

Extraction "extracted/Extracted.ml"
           toMonitor FPre FSometimeBounded FAlwaysBounded
           FSinceWithin FSinceBounded FSinceAfter
           FSinceWithinDual FSinceBoundedDual FSinceAfterDual.
