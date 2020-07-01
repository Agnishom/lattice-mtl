These proof scripts were verified with Coq 8.11.2 along with the [CoqHammer](https://github.com/lukaszcz/coqhammer) extension.

The central theorem is contained in the `Monitor.v`. The `Extraction.v` file contains an extraction script. Alternately, the OCaml code in the `extracted/` folder may also be used.

To run the experiments, go to the `extracted/` folder and run `sh experiments.sh`. Running experiments may take hours. Please configure parameters in `experiments/mytest_micro.cpp` and `experiments/Experiments.ml` as desired before running `sh experiments.sh`.
