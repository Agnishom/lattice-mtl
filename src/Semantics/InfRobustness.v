(**

This file contains:

1. Defintion of robustness using infinite traces.
2. The defintion of equivalence of formulas
3. A claim that if two traces agree in their valuations until now, our formulas cannot distinguish them in terms of their traces.

*)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.

Section InfRobustness.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.

(** `join_b lo hi f` stands for $\bigsqcup_{i=lo}^{hi} f(i)$ **)
(** `join_i start length f` stands for $\bot$ when `length` = 0,
otherwise it stands for $\bigsqcup_{i=start}^{start + length - 1} f(i)$ **)
(** similar convetions for meet **)

Fixpoint infRobustness (ϕ : Formula A) (τ : Trace) (i : nat): Val :=
  match ϕ with
  | FAtomic f => f (τ i)
  | FAnd ϕ ψ => (infRobustness ϕ τ i) ⊓ (infRobustness ψ τ i)
  | FOr ϕ ψ => (infRobustness ϕ τ i) ⊔ (infRobustness ψ τ i)
  | FSometime lo hi ψ =>
    join_b lo (min i hi) (fun j => infRobustness ψ τ (i - j))
  | FAlways lo hi ψ =>
    meet_b lo (min i hi) (fun j => infRobustness ψ τ (i - j))
  | FSometimeUnbounded lo ψ =>
    join_b lo i (fun j => infRobustness ψ τ (i - j))
  | FAlwaysUnbounded lo ψ =>
    meet_b lo i (fun j => infRobustness ψ τ (i - j))
  | FSince lo hi ϕ ψ =>
    join_b lo (min i hi) (fun j => infRobustness ψ τ (i - j)
                                 ⊓ meet_i 0 j (fun k => infRobustness ϕ τ (i - k)))
  | FSinceDual lo hi ϕ ψ =>
    meet_b lo (min i hi) (fun j => infRobustness ψ τ (i - j)
                                 ⊔ join_i 0 j (fun k => infRobustness ϕ τ (i - k)))
  | FSinceUnbounded lo ϕ ψ =>
    join_b lo i (fun j => infRobustness ψ τ (i - j)
                                 ⊓ meet_i 0 j (fun k => infRobustness ϕ τ (i - k)))
  | FSinceDualUnbounded lo ϕ ψ =>
    meet_b lo i (fun j => infRobustness ψ τ (i - j)
                                 ⊔ join_i 0 j (fun k => infRobustness ϕ τ (i - k)))
  end.

Definition equivalent (ϕ ψ : Formula A) : Prop :=
  forall τ i, infRobustness ϕ τ i = infRobustness ψ τ i.

Lemma infRobustness_prefix (ϕ : Formula A) (τ1 τ2 : Trace) (i : nat) :
  (forall j, j <= i -> τ1 j = τ2 j)
  -> infRobustness ϕ τ1 i = infRobustness ϕ τ2 i.
Proof.
  enough ((forall j, j <= i -> τ1 j = τ2 j)
          -> forall j, j <= i -> infRobustness ϕ τ1 j = infRobustness ϕ τ2 j)
    by intuition.
  induction ϕ; intros.
  - simpl. f_equal. apply H. lia.
  - simpl. specialize (IHϕ1 H j H0). specialize (IHϕ2 H j H0). congruence.
  - simpl. specialize (IHϕ1 H j H0). specialize (IHϕ2 H j H0). congruence.
  - simpl. specialize (IHϕ H). apply join_b_ext_in. intros. apply IHϕ. lia.
  - simpl. specialize (IHϕ H). apply meet_b_ext_in. intros. apply IHϕ. lia.
  - simpl. specialize (IHϕ H). apply join_b_ext_in. intros. apply IHϕ. lia.
  - simpl. specialize (IHϕ H). apply meet_b_ext_in. intros. apply IHϕ. lia.
  - simpl. specialize (IHϕ1 H). specialize (IHϕ2 H).
    apply join_b_ext_in. intros. f_equal. apply IHϕ2. lia.
    apply meet_i_ext_in. intros. apply IHϕ1. lia.
  - simpl. specialize (IHϕ1 H). specialize (IHϕ2 H).
    apply meet_b_ext_in. intros. f_equal. apply IHϕ2. lia.
    apply join_i_ext_in. intros. apply IHϕ1. lia.
  - simpl. specialize (IHϕ1 H). specialize (IHϕ2 H).
    apply join_b_ext_in. intros. f_equal. apply IHϕ2. lia.
    apply meet_i_ext_in. intros. apply IHϕ1. lia.
  - simpl. specialize (IHϕ1 H). specialize (IHϕ2 H).
    apply meet_b_ext_in. intros. f_equal. apply IHϕ2. lia.
    apply join_i_ext_in. intros. apply IHϕ1. lia.
Qed.


End InfRobustness.

Arguments infRobustness {Val A lattice_val boundedLattice_val}.
Arguments equivalent {Val A lattice_val boundedLattice_val}.

Open Scope list_scope.
