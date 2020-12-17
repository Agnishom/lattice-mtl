Require Import Lattice.
Require Import Monoid.

Section Formula.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Inductive Formula {A : Type} : Type :=
| FAtomic : (A -> Val) -> Formula
| FAnd : Formula -> Formula -> Formula
| FOr : Formula -> Formula -> Formula
| FSometime : nat -> nat -> Formula -> Formula
| FAlways : nat -> nat -> Formula -> Formula
| FSometimeUnbounded : nat -> Formula -> Formula
| FAlwaysUnbounded : nat -> Formula -> Formula
| FSince : nat -> nat -> Formula -> Formula -> Formula
| FSinceDual : nat -> nat -> Formula -> Formula -> Formula
| FSinceUnbounded : nat -> Formula -> Formula -> Formula
| FSinceDualUnbounded : nat -> Formula -> Formula -> Formula
.

Definition FDelay {A : Type} (i : nat) (ϕ : Formula) :=
  @FSometime A i i ϕ.
Definition FDelayDual {A : Type} (i : nat) (ϕ : Formula) :=
  @FAlways A i i ϕ.

End Formula.

Arguments Formula {Val}.
Arguments FAtomic {Val A}.
Arguments FAnd {Val A}.
Arguments FOr {Val A}.
Arguments FSometime {Val A}.
Arguments FAlways {Val A}.
Arguments FSometimeUnbounded {Val A}.
Arguments FAlwaysUnbounded {Val A}.
Arguments FSince {Val A}.
Arguments FSinceDual {Val A}.
Arguments FSinceUnbounded {Val A}.
Arguments FSinceDualUnbounded {Val A}.
Arguments FDelay {Val A}.
Arguments FDelayDual {Val A}.
