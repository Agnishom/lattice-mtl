Require Import Coq.Lists.List.

From Algebra Require Import Monoid.
From Algebra Require Import Lattice.
From Syntax Require Import Formula.
From Semantics Require Import Robustness.
From Semantics Require Import InfRobustness.
From NonEmptyList Require Import NonEmptyList.
Require Import Mealy.
Require Import Monitor.
From Lemmas Require Import Lemmas.

Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import ssreflect.

Section NewMonitor.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition monSinceUp (n : nat) : @Monitor Val (Val * Val) :=
  @monAnd Val (Val * Val) lattice_val
    (monSince (monAtomic fst) (monAtomic snd))
    (monSometimeBounded n (monAtomic snd)).

Lemma monSinceUp_correcntess:
  forall n, implements (monSinceUp n) (FSince 0 n (FAtomic fst) (FAtomic snd)).
Proof.
  unfold implements. intros.
  remember (FSince _ _ _ _) as f.
  rewrite -> robustness_eq with (ψ := normalize f) by now apply normalize_correctness.
  subst. simpl. unfold monSinceUp.
  apply monAnd_correctness.
  - apply monSince_correctness. auto.
    apply monAtomic_correctness.
    apply monAtomic_correctness.
  - apply monSometimeBounded_correctness.
    apply monAtomic_correctness.
Qed.

Lemma fst_extend_neZip {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
  neLength σ = neLength τ
  -> forall i, fst (extend (neZip σ τ) i) = extend σ i.
Proof.

Admitted.

Lemma snd_extend_neZip {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
  neLength σ = neLength τ
  -> forall i, snd (extend (neZip σ τ) i) = extend τ i.
Proof.

Admitted.


Lemma monSinceUp_composition (m n : Monitor) (ϕ ψ : Formula A):
  implements m ϕ
  -> implements n ψ
  -> forall a, implements ((mPar m n) >> monSinceUp a) (FSince 0 a ϕ ψ).
Proof.
  unfold implements.
  intros.
  rewrite mPar_mCompose.
  rewrite monSinceUp_correcntess.
  unfold robustness. simpl.
  rewrite length_toList.
  rewrite -> neZip_neLength
    by now repeat rewrite gCollect_neLength; auto.
  rewrite gCollect_neLength.
  rewrite length_toList.
  under join_b_ext_in => j.
  rewrite -> snd_extend_neZip
    by now repeat rewrite gCollect_neLength; auto.
  intros.
  rewrite -> (extend_gCollect Val A) with (ϕ0 := ψ).
  under meet_i_ext_in => k.
  intros. rewrite -> fst_extend_neZip
    by now repeat rewrite gCollect_neLength; auto.
  rewrite -> (extend_gCollect Val A) with (ϕ0 := ϕ).
  over.
  auto.
  rewrite <- length_toList. pose proof (length_toList1 σ). lia.
  over.
  auto.
  rewrite <- length_toList. pose proof (length_toList1 σ). lia.
  auto.
Qed.


End NewMonitor.
