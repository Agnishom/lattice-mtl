From Syntax Require Formula.
From Monitor Require ToMonitor.

Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlNatInt.
Extraction Language OCaml.

Extraction "../extracted/LatticeMtl.ml" ToMonitor.toMonitor.
