From Syntax Require Formula.
From Monitor Require Monitor.

Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlNatInt.
Extraction Language Ocaml.

Extraction "../extracted/LatticeMtl.ml" Monitor.toMonitor.
