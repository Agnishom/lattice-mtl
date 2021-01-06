Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.

Require Import InfRobustness.

Section SimpleProperties.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.

Lemma fdelay_correctness :
  forall (ϕ : Formula A) τ jj i, infRobustness (FDelay jj ϕ) τ i =
              if (jj <=? i) then (infRobustness ϕ τ (i - jj))
              else bottom.
Proof.
  intros. unfold FDelay.
  simpl infRobustness at 1.
  destruct (PeanoNat.Nat.le_gt_cases jj i).
  - replace (min i jj) with jj by lia.
    apply Nat.leb_le in H. rewrite H.
    unfold join_b. unfold op_b.
    replace (S jj - jj) with 1 by lia.
    unfold op_i. simpl.
    apply finite_op_singleton.
  - replace (min i jj) with i by lia.
    unfold join_b. unfold op_b.
    replace (S i - jj) with 0 by lia.
    apply Compare_dec.leb_iff_conv in H. rewrite H.
    unfold op_i. auto.
Qed.

Lemma fdelayDual_correctness :
  forall (ϕ : Formula A) τ jj i, infRobustness (FDelayDual jj ϕ) τ i =
              if (jj <=? i) then (infRobustness ϕ τ (i - jj))
              else top.
Proof.
  intros. unfold FDelayDual.
  simpl infRobustness at 1.
  destruct (PeanoNat.Nat.le_gt_cases jj i).
  - replace (min i jj) with jj by lia.
    apply Nat.leb_le in H. rewrite H.
    unfold meet_b. unfold op_b.
    replace (S jj - jj) with 1 by lia.
    unfold op_i. simpl.
    apply finite_op_singleton.
  - replace (min i jj) with i by lia.
    unfold meet_b. unfold op_b.
    replace (S i - jj) with 0 by lia.
    apply Compare_dec.leb_iff_conv in H. rewrite H.
    unfold op_i. auto.
Qed.

Lemma fSometime_hi_lo :
  forall (ϕ : Formula A) τ lo hi i,
    lo > hi -> infRobustness (FSometime lo hi ϕ) τ i = bottom.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold join_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fAlways_hi_lo :
  forall (ϕ : Formula A) τ lo hi i,
    lo > hi -> infRobustness (FAlways lo hi ϕ) τ i = top.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold meet_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSince_hi_lo :
  forall (ϕ ψ : Formula A) τ lo hi i,
    lo > hi -> infRobustness (FSince lo hi ϕ ψ) τ i = bottom.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold join_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSinceDual_hi_lo :
  forall (ϕ ψ : Formula A) τ lo hi i,
    lo > hi -> infRobustness (FSinceDual lo hi ϕ ψ) τ i = top.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold meet_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSometime_i_lo  :
  forall (ϕ : Formula A) τ lo hi i,
    lo > i -> infRobustness (FSometime lo hi ϕ) τ i = bottom.
Proof.
  intros.
  destruct (PeanoNat.Nat.le_gt_cases lo hi).
  - destruct (PeanoNat.Nat.lt_ge_cases i hi).
    + simpl. replace (min i hi) with i by lia.
      unfold join_b. unfold op_b.
      replace (S i - lo) with 0 by lia.
      easy.
    + simpl. replace (min i hi) with hi by lia.
      unfold join_b. unfold op_b.
      replace (S hi - lo) with 0 by lia.
      easy.
  - apply fSometime_hi_lo. lia.
Qed.

Lemma fSince_i_lo :
  forall (ϕ ψ : Formula A) τ lo hi i,
    lo > i -> infRobustness (FSince lo hi ϕ ψ) τ i = bottom.
Proof.
intros.
  destruct (PeanoNat.Nat.le_gt_cases lo hi).
  - destruct (PeanoNat.Nat.lt_ge_cases i hi).
    + simpl. replace (min i hi) with i by lia.
      unfold join_b. unfold op_b.
      replace (S i - lo) with 0 by lia.
      easy.
    + simpl. replace (min i hi) with hi by lia.
      unfold join_b. unfold op_b.
      replace (S hi - lo) with 0 by lia.
      easy.
  - apply fSince_hi_lo. lia.
Qed.

Lemma fSinceDual_i_lo :
  forall (ϕ ψ : Formula A) τ lo hi i,
    lo > i -> infRobustness (FSinceDual lo hi ϕ ψ) τ i = top.
Proof.
intros.
  destruct (PeanoNat.Nat.le_gt_cases lo hi).
  - destruct (PeanoNat.Nat.lt_ge_cases i hi).
    + simpl. replace (min i hi) with i by lia.
      unfold meet_b. unfold op_b.
      replace (S i - lo) with 0 by lia.
      easy.
    + simpl. replace (min i hi) with hi by lia.
      unfold meet_b. unfold op_b.
      replace (S hi - lo) with 0 by lia.
      easy.
  - apply fSinceDual_hi_lo. lia.
Qed.

Lemma fSometimeUnbounded_i_lo :
  forall (ϕ : Formula A) τ lo i,
    lo > i ->
    infRobustness (FSometimeUnbounded lo ϕ) τ i = bottom.
Proof.
  intros.
  simpl.
  unfold join_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fSinceUnbounded_i_lo :
  forall (ϕ ψ : Formula A) τ lo i,
    lo > i ->
    infRobustness (FSinceUnbounded lo ϕ ψ) τ i = bottom.
Proof.
  intros.
  simpl.
  unfold join_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fSinceDualUnbounded_i_lo :
  forall (ϕ ψ : Formula A) τ lo i,
    lo > i ->
    infRobustness (FSinceDualUnbounded lo ϕ ψ) τ i = top.
Proof.
  intros.
  simpl.
  unfold meet_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fAlways_i_lo :
  forall (ϕ : Formula A) τ lo hi i,
    lo > i -> infRobustness (FAlways lo hi ϕ) τ i = top.
Proof.
  intros.
  destruct (PeanoNat.Nat.le_gt_cases lo hi).
  - destruct (PeanoNat.Nat.lt_ge_cases i hi).
    + simpl. replace (min i hi) with i by lia.
      unfold meet_b. unfold op_b.
      replace (S i - lo) with 0 by lia.
      easy.
    + simpl. replace (min i hi) with hi by lia.
      unfold meet_b. unfold op_b.
      replace (S hi - lo) with 0 by lia.
      easy.
  - apply fAlways_hi_lo. lia.
Qed.

Lemma fAlwaysUnbounded_i_lo :
  forall (ϕ : Formula A) τ lo i,
    lo > i ->
    infRobustness (FAlwaysUnbounded lo ϕ) τ i = top.
Proof.
  intros.
  simpl.
  unfold meet_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

End SimpleProperties.
