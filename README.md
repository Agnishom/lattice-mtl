# lattice-mtl
A Verified Online Monitor for Metric Temporal Logic with Quantitative Semantics ([Extended Version](extended-draft.pdf))

```
@InProceedings{ChattopadhyayM20,
  author="Chattopadhyay, Agnishom
      and Mamouras, Konstantinos",
  editor="Deshmukh, Jyotirmoy
      and Ni{\v{c}}kovi{\'{c}}, Dejan",
  title="A Verified Online Monitor for Metric Temporal Logic with Quantitative Semantics",
  booktitle="Runtime Verification",
  year="2020",
  publisher="Springer International Publishing",
  address="Cham",
  pages="383--403",
}
```

## Usage as a library

To use this as a library, see the instructions in `extracted/README.md`

## Extraction

The Extracted Code can be found in `extracted/LatticeMtl.ml` with some examples of usage in `extracted/Examples.ml`. To re-run the extraction (and verification) process:

```
cd src/
make Makefile.coq
make
```

The current version of the proof was checked using Coq 8.12.1.

## Organization of the Proof

The `toMonitor : Formula -> Monitor` is defined in [`Monitor/ToMonitor.v`](https://github.com/Agnishom/lattice-mtl/blob/master/src/Monitor/ToMonitor.v#L776). The semantics of the formulae are available in [`Semantics/InfRobustness.v`](https://github.com/Agnishom/lattice-mtl/blob/master/src/Semantics/InfRobustness.v#L21) and the main theorem, `toMonitor_correctness` can be found in [`Monitor/ToMonitor.v`](https://github.com/Agnishom/lattice-mtl/blob/master/src/Monitor/ToMonitor.v#L821).

Below is a brief discussion of the organization of the proof:

* `Lemmas/`: Various useful auxilary functions. Relevant lemmas.
* `NonEmptyList/`: Type of non-empty lists.
* `Algebra/`:
  - `Algebra/Monoid.v`:  Definition of Monoids. Extending monoid operations to finite lists.
  - `Algebra/Lattice.v`: Lattices. Bounded, Distributive Lattices. Order Theoretic Properties of Lattices.
* `Syntax/`:
  - `Syntax/Formula.v`: Syntax of Past-time MTL formulas. Some syntactic sugar.
  - `Syntax/Normal.v`: Definition of and conversion into normal forms. The resulting formulae only contain certain constructs
* `Semantics/`:
  - `Semantics/InfRobustness.v`: Semantics of MTL formulas on infinite traces.
  - `Semantics/Robustness.v`: Semantics on non-empty lists (defined via their extension to infinite traces).
  - `Semantics/SimpleProperties.v`: Simple properties of some degenerate MTL formulas.
  - `Semantics/Incremental.v`: Incremental derivations of semantic values. Used to construct the monitors.
  - `Semantics/SinceRewrite.v`: Translating `S_[0,a]` to `S` and `Sometime_[0,a]`.
  - `Semantics/Equivalences.v`: Other MTL identities.
  - `Semantics/NormalizeCorrect.v`: Correctness of the normal forms.
* `Monitor/`
  - `Monitor/Mealy.v`: Mealy Machines. Denotations. Composition. Unbounded Aggregation.
  - `Monitor/Queue.v`: Queue. Implementation of `Sometime_[n,n]`
  - `Monitor/AggQueue.v`: Sliding window aggregation. Implementation of `Sometime_[0,n]`.
  - `Monitor/Monitor.v`: Definition of Monitors. `implements` relation. Combinators for building blocks.
  - `Monitor/ToMonitor.v`: Translating Formulas to Monitors. Proof of Correctness.
* `Extract/`: Extraction to OCaml.
