Require Import Coq.Lists.List.

Require Import Lattice.
Require Import InfRobustness.
Require Import NonEmptyList.
Require Import Formula.

Require Import Lia.

Section Robustness.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition extends (τ : Trace A) (σ : nonEmpty A) : Prop :=
  forall i, i < length (toList σ) ->
       nth_error (rev (toList σ)) i = Some (τ i).

Lemma extends_infRobustness (σ : nonEmpty A) (τ1 τ2 : Trace A) :
  extends τ1 σ
  -> extends τ2 σ
  -> forall i, i < length (toList σ)
  -> forall ϕ, infRobustness ϕ τ1 i = infRobustness ϕ τ2 i.
Proof.
  intros. apply infRobustness_prefix.
  intros. unfold extends in *.
  specialize (H j). specialize (H0 j).
  assert (j < length (toList σ)) by lia.
  specialize (H H3). specialize (H0 H3).
  f_equal.
Qed.

Definition extend (σ : nonEmpty A) : Trace A :=
  fun i => nth i (rev (toList σ)) (latest σ).

Lemma extend_extends (σ : nonEmpty A) :
  extends (extend σ) σ.
Proof.
  unfold extends. unfold extend.
  intros.
  rewrite nth_error_nth' with (d := (latest σ)). auto.
  now rewrite rev_length.
Qed.

Definition robustness (ϕ : Formula A) (σ : nonEmpty A) : Val :=
  infRobustness ϕ (extend σ) (pred (length (toList σ))).

End Robustness.

Arguments robustness {Val A lattice_val boundedLattice_val}.
Arguments extends {A}.
Arguments extend {A}.
