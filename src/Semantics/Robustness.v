(**

This file contains:

1. Defintion of Robustness for non-empty (finite) lists
  - using the defintion over infinite traces, see [robustness].
2. Definition of an infinite trace extending a non-empty list.
  - and some consequences of this phenomena.

*)

Require Import Coq.Lists.List.

From Algebra Require Import Lattice.
Require Export InfRobustness.
From NonEmptyList Require Import NonEmptyList.
From Syntax Require Import Formula.
From Syntax Require Export Normal.
Require Export NormalizeCorrect.
Require Export Incremental.
Require Export SimpleProperties.

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

(** Given any finite, non-empty trace σ, we can consider an extension of
    σ which is obtained by repeating the latest element of σ infinitely
    many times. We use this to define the robustness of σ itself.

    This definition is sound because of the facts captured in the Lemmas
    `extend_extends` and `extends_infRobustness` above **)

Definition robustness (ϕ : Formula A) (σ : nonEmpty A) : Val :=
  infRobustness ϕ (extend σ) (pred (length (toList σ))).

Lemma robustness_eq (ϕ ψ : Formula A) (σ : nonEmpty A) :
  (forall τ i, infRobustness ϕ τ i = infRobustness ψ τ i)
  -> robustness ϕ σ = robustness ψ σ.
Proof.
  intros. unfold robustness.
  apply H.
Qed.

End Robustness.

Arguments robustness {Val A lattice_val boundedLattice_val}.
Arguments extends {A}.
Arguments extend {A}.
