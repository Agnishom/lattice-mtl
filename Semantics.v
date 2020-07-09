From Hammer Require Import Hammer.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

Require Import Lattice.
Require Import Monoid.

Section Semantics.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace (A : Type) := nat -> A.

Inductive Formula {A : Type} : Type :=
| FAtomic : (A -> Val) -> Formula
| FSometime : nat -> nat -> Formula -> Formula
| FAlways : nat -> nat -> Formula -> Formula
| FSometimeUnbounded : nat -> Formula -> Formula
| FAlwaysUnbounded : nat -> Formula -> Formula
| FSince : nat -> nat -> Formula -> Formula -> Formula
| FSinceDual : nat -> nat -> Formula -> Formula -> Formula
| FSinceUnbounded : nat -> Formula -> Formula -> Formula
| FSinceDualUnbounded : nat -> Formula -> Formula -> Formula
.

Fixpoint robustness {A : Type} (ϕ : @Formula A) (τ : Trace A) (i : nat): Val :=
  match ϕ with
  | FAtomic f => f (τ i)
  | FSometime lo hi ψ =>
    join_b lo (min i hi) (fun j => robustness ψ τ (i - j))
  | FAlways lo hi ψ =>
    meet_b lo (min i hi) (fun j => robustness ψ τ (i - j))
  | FSometimeUnbounded lo ψ =>
    join_b lo i (fun j => robustness ψ τ (i - j))
  | FAlwaysUnbounded lo ψ =>
    meet_b lo i (fun j => robustness ψ τ (i - j))
  | FSince lo hi ϕ ψ =>
    join_b lo (min i hi) (fun j => robustness ψ τ (i - j)
                                 ⊓ meet_i 0 j (fun k => robustness ψ τ (i - k)))
  | FSinceDual lo hi ϕ ψ =>
    meet_b lo (min i hi) (fun j => robustness ψ τ (i - j)
                                 ⊔ join_i 0 j (fun k => robustness ψ τ (i - k)))
  | FSinceUnbounded lo ϕ ψ =>
    join_b lo i (fun j => robustness ψ τ (i - j)
                                 ⊓ meet_i 0 j (fun k => robustness ψ τ (i - k)))
  | FSinceDualUnbounded lo ϕ ψ =>
    meet_b lo i (fun j => robustness ψ τ (i - j)
                                 ⊔ join_i 0 j (fun k => robustness ψ τ (i - k)))
  end.

Definition FDelay {A : Type} (i : nat) (ϕ : @Formula A) :=
  FSometime i i ϕ.
Definition FDelayDual {A : Type} (i : nat) (ϕ : @Formula A) :=
  FAlways i i ϕ.

Lemma fdelay_correctness {A : Type} :
  forall (ϕ : @Formula A) τ jj i, robustness (FDelay jj ϕ) τ i =
              if (jj <=? i) then (robustness ϕ τ (i - jj))
              else bottom.
Proof.
  intros. unfold FDelay.
  simpl robustness at 1.
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

Lemma fdelayDual_correctness {A : Type} :
  forall (ϕ : @Formula A) τ jj i, robustness (FDelayDual jj ϕ) τ i =
              if (jj <=? i) then (robustness ϕ τ (i - jj))
              else top.
Proof.
  intros. unfold FDelayDual.
  simpl robustness at 1.
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

Lemma fSometime_hi_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo > hi -> robustness (FSometime lo hi ϕ) τ i = bottom.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold join_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fAlways_hi_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo > hi -> robustness (FAlways lo hi ϕ) τ i = top.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold meet_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSince_hi_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo hi i,
    lo > hi -> robustness (FSince lo hi ϕ ψ) τ i = bottom.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold join_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSinceDual_hi_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo hi i,
    lo > hi -> robustness (FSinceDual lo hi ϕ ψ) τ i = top.
Proof.
  intros. simpl. remember (min i hi) as x.
  assert (lo > x) by lia.
  unfold meet_b. unfold op_b.
  replace (S x - lo) with 0 by lia.
  auto.
Qed.

Lemma fSometime_i_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo > i -> robustness (FSometime lo hi ϕ) τ i = bottom.
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

Lemma fSince_i_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo hi i,
    lo > i -> robustness (FSince lo hi ϕ ψ) τ i = bottom.
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

Lemma fSinceDual_i_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo hi i,
    lo > i -> robustness (FSinceDual lo hi ϕ ψ) τ i = top.
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

Lemma fSometimeUnbounded_i_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo i,
    lo > i ->
    robustness (FSometimeUnbounded lo ϕ) τ i = bottom.
Proof.
  intros.
  simpl.
  unfold join_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fSinceUnbounded_i_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo i,
    lo > i ->
    robustness (FSinceUnbounded lo ϕ ψ) τ i = bottom.
Proof.
  intros.
  simpl.
  unfold join_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fSinceDualUnbounded_i_lo {A : Type} :
  forall (ϕ ψ : @Formula A) τ lo i,
    lo > i ->
    robustness (FSinceDualUnbounded lo ϕ ψ) τ i = top.
Proof.
  intros.
  simpl.
  unfold meet_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma fAlways_i_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo > i -> robustness (FAlways lo hi ϕ) τ i = top.
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

Lemma fAlwaysUnbounded_i_lo {A : Type} :
  forall (ϕ : @Formula A) τ lo i,
    lo > i ->
    robustness (FAlwaysUnbounded lo ϕ) τ i = top.
Proof.
  intros.
  simpl.
  unfold meet_b. unfold op_b.
  replace (S i - lo) with 0 by lia.
  easy.
Qed.

Lemma sometime_delay_bounded {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo <= hi ->
    robustness (FSometime lo hi ϕ) τ i = robustness (FDelay lo (FSometime 0 (hi - lo) ϕ)) τ i.
Proof.
  intros.
  rewrite fdelay_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H0' := H0). rewrite <- Nat.leb_le in H0'. rewrite H0'.
    clear H0'.
    simpl robustness. unfold join_b.
    remember (min i hi) as x.
    replace (min (i - lo) (hi - lo)) with (x - lo) by lia.
    replace (lo) with (0 + lo) at 1 by lia.
    replace x with ((x - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => robustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fSometime_i_lo by lia.
    rewrite <- Nat.leb_gt in H0. now rewrite H0.
Qed.

Lemma always_delay_bounded {A : Type} :
  forall (ϕ : @Formula A) τ lo hi i,
    lo <= hi ->
    robustness (FAlways lo hi ϕ) τ i = robustness (FDelayDual lo (FAlways 0 (hi - lo) ϕ)) τ i.
Proof.
  intros.
  rewrite fdelayDual_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H0' := H0). rewrite <- Nat.leb_le in H0'. rewrite H0'.
    clear H0'.
    simpl robustness. unfold meet_b.
    remember (min i hi) as x.
    replace (min (i - lo) (hi - lo)) with (x - lo) by lia.
    replace (lo) with (0 + lo) at 1 by lia.
    replace x with ((x - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => robustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fAlways_i_lo by lia.
    rewrite <- Nat.leb_gt in H0. now rewrite H0.
Qed.

Lemma sometime_delay_unbounded {A : Type} :
  forall (ϕ : @Formula A) τ lo i,
    robustness (FSometimeUnbounded lo ϕ) τ i
    = robustness (FDelay lo (FSometimeUnbounded 0 ϕ)) τ i.
Proof.
  intros.
  rewrite fdelay_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H' := H). rewrite <- Nat.leb_le in H'. rewrite H'.
    clear H'.
    simpl robustness. unfold join_b.
    replace (lo) with (0 + lo) at 1 by lia.
    replace i with ((i - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => robustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fSometimeUnbounded_i_lo by lia.
    rewrite <- Nat.leb_gt in H. now rewrite H.
Qed.

Lemma always_delay_unbounded {A : Type} :
  forall (ϕ : @Formula A) τ lo i,
    robustness (FAlwaysUnbounded lo ϕ) τ i
    = robustness (FDelayDual lo (FAlwaysUnbounded 0 ϕ)) τ i.
Proof.
  intros.
  rewrite fdelayDual_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H' := H). rewrite <- Nat.leb_le in H'. rewrite H'.
    clear H'.
    simpl robustness. unfold meet_b.
    replace (lo) with (0 + lo) at 1 by lia.
    replace i with ((i - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => robustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fAlwaysUnbounded_i_lo by lia.
    rewrite <- Nat.leb_gt in H. intros. now rewrite H.
Qed.

