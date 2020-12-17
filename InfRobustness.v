From Hammer Require Import Hammer.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

Require Import Lattice.
Require Import Monoid.
Require Import Formula.

Section InfRobustness.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.

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

Lemma sometime_delay_bounded :
  forall (ϕ : Formula A) τ lo hi i,
    lo <= hi ->
    infRobustness (FSometime lo hi ϕ) τ i = infRobustness (FDelay lo (FSometime 0 (hi - lo) ϕ)) τ i.
Proof.
  intros.
  rewrite fdelay_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H0' := H0). rewrite <- Nat.leb_le in H0'. rewrite H0'.
    clear H0'.
    simpl infRobustness. unfold join_b.
    remember (min i hi) as x.
    replace (min (i - lo) (hi - lo)) with (x - lo) by lia.
    replace (lo) with (0 + lo) at 1 by lia.
    replace x with ((x - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => infRobustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fSometime_i_lo by lia.
    rewrite <- Nat.leb_gt in H0. now rewrite H0.
Qed.

Lemma always_delay_bounded :
  forall (ϕ : Formula A) τ lo hi i,
    lo <= hi ->
    infRobustness (FAlways lo hi ϕ) τ i = infRobustness (FDelayDual lo (FAlways 0 (hi - lo) ϕ)) τ i.
Proof.
  intros.
  rewrite fdelayDual_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H0' := H0). rewrite <- Nat.leb_le in H0'. rewrite H0'.
    clear H0'.
    simpl infRobustness. unfold meet_b.
    remember (min i hi) as x.
    replace (min (i - lo) (hi - lo)) with (x - lo) by lia.
    replace (lo) with (0 + lo) at 1 by lia.
    replace x with ((x - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => infRobustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fAlways_i_lo by lia.
    rewrite <- Nat.leb_gt in H0. now rewrite H0.
Qed.

Lemma sometime_delay_unbounded :
  forall (ϕ : Formula A) τ lo i,
    infRobustness (FSometimeUnbounded lo ϕ) τ i
    = infRobustness (FDelay lo (FSometimeUnbounded 0 ϕ)) τ i.
Proof.
  intros.
  rewrite fdelay_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H' := H). rewrite <- Nat.leb_le in H'. rewrite H'.
    clear H'.
    simpl infRobustness. unfold join_b.
    replace (lo) with (0 + lo) at 1 by lia.
    replace i with ((i - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => infRobustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fSometimeUnbounded_i_lo by lia.
    rewrite <- Nat.leb_gt in H. now rewrite H.
Qed.

Lemma always_delay_unbounded :
  forall (ϕ : Formula A) τ lo i,
    infRobustness (FAlwaysUnbounded lo ϕ) τ i
    = infRobustness (FDelayDual lo (FAlwaysUnbounded 0 ϕ)) τ i.
Proof.
  intros.
  rewrite fdelayDual_correctness.
  destruct (PeanoNat.Nat.le_gt_cases lo i).
  - assert (H' := H). rewrite <- Nat.leb_le in H'. rewrite H'.
    clear H'.
    simpl infRobustness. unfold meet_b.
    replace (lo) with (0 + lo) at 1 by lia.
    replace i with ((i - lo) + lo) at 1 by lia.
    rewrite <- op_b_shift_ext with (g := (fun j => infRobustness ϕ τ (i - lo - j))) (h := lo).
    reflexivity.
    intros. f_equal. lia.
  - rewrite ->fAlwaysUnbounded_i_lo by lia.
    rewrite <- Nat.leb_gt in H. intros. now rewrite H.
Qed.

Lemma since_always_bounded :
  forall (ϕ ψ : Formula A) τ a b i,
    a < b ->
    a < i ->
    infRobustness (FSince (S a) b ϕ ψ) τ i
    = infRobustness (FAnd (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) (FAlways 0 a ϕ)) τ i.
Proof.
  intros. simpl infRobustness at 1.
  unfold join_b.
  replace (S a) with (1 + a) at 1 by lia.
  replace (min i b) with ((min (i - a) (b - a)) + a) by lia.
  rewrite <- op_b_shift_ext_in with
      (lo := 1)
      (hi := min (i - a) (b - a))
      (g := (fun j : nat => infRobustness ψ τ (i - a - j) ⊓ meet_i 0 (j + a) (fun k : nat => infRobustness ϕ τ (i - k)))) by now intros; f_equal; f_equal; lia.
  under op_b_ext_in => j.
  intros.
  unfold meet_i.
  replace (j + a) with (S a + (j - 1)) by lia.
  rewrite -> op_i_app with
      (l1 := S a)
      (l2 := (j - 1)).
  simpl.
  rewrite ->meet_comm with (x := (op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)))).
  rewrite <-meet_assoc.
  replace ( op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)) )
    with
      (infRobustness (FAlways 0 a ϕ) τ i)
    by now simpl; unfold meet_b; unfold op_b; f_equal; lia.
  over.
  replace (op_b Val 1 (Init.Nat.min (i - a) (b - a))
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
       ⊓ infRobustness (FAlways 0 a ϕ) τ i))
    with
      (join_b 1 (Init.Nat.min (i - a) (b - a))
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
     ⊓ infRobustness (FAlways 0 a ϕ) τ i)) by auto.
  rewrite ->join_b_distr_ext_in
  with (g := (fun j : nat =>
                (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))))
       (v := (infRobustness (FAlways 0 a ϕ) τ i)) by now intros; auto; lia.
  under join_b_ext_in => j.
  intros.
  replace (S a) with (0 + S a) by lia.
  rewrite <- op_i_shift_ext_in with
      (f := (fun k : nat => infRobustness ϕ τ (i - k)))
      (g := (fun k : nat => infRobustness ϕ τ (i - (S a) - k)) )
  by now intros; f_equal; lia.
  over.
  replace 1 with (0 + 1) at 1 by lia.
  replace (min (i - a) (b - a)) with (min (i - S a) (b - S a) + 1) by lia.
  unfold join_b.
  rewrite <- op_b_shift_ext_in with
      (g := (fun j : nat =>
               infRobustness ψ τ (i - (S a) - j) ⊓ op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - S a - k))))
    by now intros; f_equal; f_equal; lia.
  change (infRobustness (FAnd (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) (FAlways 0 a ϕ)) τ i)
    with (infRobustness (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) τ i ⊓ infRobustness (FAlways 0 a ϕ) τ i).
  f_equal.
  rewrite fdelay_correctness.
  assert (S a <= i) by lia. rewrite <-Nat.leb_le in H1. rewrite H1. clear H1.
  auto.
Qed.

Lemma sinceDual_sometime_bounded :
  forall (ϕ ψ : Formula A) τ a b i,
    a < b ->
    a < i ->
    infRobustness (FSinceDual (S a) b ϕ ψ) τ i
    = infRobustness (FOr (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) (FSometime 0 a ϕ)) τ i.
Proof.
  intros. simpl infRobustness at 1.
  unfold meet_b.
  replace (S a) with (1 + a) at 1 by lia.
  replace (min i b) with ((min (i - a) (b - a)) + a) by lia.
  rewrite <- op_b_shift_ext_in with
      (lo := 1)
      (hi := min (i - a) (b - a))
      (g := (fun j : nat => infRobustness ψ τ (i - a - j) ⊔ join_i 0 (j + a) (fun k : nat => infRobustness ϕ τ (i - k)))) by now intros; f_equal; f_equal; lia.
  under op_b_ext_in => j.
  intros.
  unfold join_i.
  replace (j + a) with (S a + (j - 1)) by lia.
  rewrite -> op_i_app with
      (l1 := S a)
      (l2 := (j - 1)).
  simpl.
  rewrite ->join_comm with (x := (op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)))).
  rewrite <-join_assoc.
  replace ( op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)) )
    with
      (infRobustness (FSometime 0 a ϕ) τ i)
    by now simpl; unfold join_b; unfold op_b; f_equal; lia.
  over.
  replace (op_b Val 1 (Init.Nat.min (i - a) (b - a))
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
       ⊔ infRobustness (FSometime 0 a ϕ) τ i))
    with
      (meet_b 1 (Init.Nat.min (i - a) (b - a))
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
     ⊔ infRobustness (FSometime 0 a ϕ) τ i)) by auto.
  rewrite ->meet_b_distr_ext_in
  with (g := (fun j : nat =>
                (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))))
       (v := (infRobustness (FSometime 0 a ϕ) τ i)) by now intros; auto; lia.
  under meet_b_ext_in => j.
  intros.
  replace (S a) with (0 + S a) by lia.
  rewrite <- op_i_shift_ext_in with
      (f := (fun k : nat => infRobustness ϕ τ (i - k)))
      (g := (fun k : nat => infRobustness ϕ τ (i - (S a) - k)) )
  by now intros; f_equal; lia.
  over.
  replace 1 with (0 + 1) at 1 by lia.
  replace (min (i - a) (b - a)) with (min (i - S a) (b - S a) + 1) by lia.
  unfold meet_b.
  rewrite <- op_b_shift_ext_in with
      (g := (fun j : nat =>
               infRobustness ψ τ (i - (S a) - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val) 0 j (fun k : nat => infRobustness ϕ τ (i - S a - k))))
    by now intros; f_equal; f_equal; lia.
  change (infRobustness (FOr (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) (FSometime 0 a ϕ)) τ i)
    with (infRobustness (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) τ i ⊔ infRobustness (FSometime 0 a ϕ) τ i).
  f_equal.
  rewrite fdelayDual_correctness.
  assert (S a <= i) by lia. rewrite <-Nat.leb_le in H1. rewrite H1. clear H1.
  auto.
Qed.

Lemma since_always_unbounded :
  forall (ϕ ψ : Formula A) τ a i,
    a < i ->
    infRobustness (FSinceUnbounded (S a) ϕ ψ) τ i
    = infRobustness (FAnd (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) (FAlways 0 a ϕ)) τ i.
Proof.
  intros. simpl infRobustness at 1.
  unfold join_b.
  replace (S a) with (1 + a) at 1 by lia.
  replace i with ((i - a) + a) at 1 by lia.
  rewrite <- op_b_shift_ext_in with
      (lo := 1)
      (hi := i - a)
      (g := (fun j : nat => infRobustness ψ τ (i - a - j) ⊓ meet_i 0 (j + a) (fun k : nat => infRobustness ϕ τ (i - k)))) by now intros; f_equal; f_equal; lia.
  under op_b_ext_in => j.
  intros.
  unfold meet_i.
  replace (j + a) with (S a + (j - 1)) by lia.
  rewrite -> op_i_app with
      (l1 := S a)
      (l2 := (j - 1)).
  simpl.
  rewrite ->meet_comm with (x := (op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)))).
  rewrite <-meet_assoc.
  replace ( op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)) )
    with
      (infRobustness (FAlways 0 a ϕ) τ i)
    by now simpl; unfold meet_b; unfold op_b; f_equal; lia.
  over.
  replace (op_b Val 1 (i - a)
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
       ⊓ infRobustness (FAlways 0 a ϕ) τ i))
    with
   (join_b 1 (i - a)
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
     ⊓ infRobustness (FAlways 0 a ϕ) τ i)) by auto.
  rewrite ->join_b_distr_ext_in
  with (g := (fun j : nat =>
                (infRobustness ψ τ (i - a - j) ⊓ op_i Val (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))))
       (v := (infRobustness (FAlways 0 a ϕ) τ i)) by now intros; auto; lia.
  under join_b_ext_in => j.
  intros.
  replace (S a) with (0 + S a) by lia.
  rewrite <- op_i_shift_ext_in with
      (f := (fun k : nat => infRobustness ϕ τ (i - k)))
      (g := (fun k : nat => infRobustness ϕ τ (i - (S a) - k)) )
  by now intros; f_equal; lia.
  over.
  replace 1 with (0 + 1) at 1 by lia.
  replace (i - a) with ((i - S a) + 1) by lia.
  unfold join_b.
  rewrite <- op_b_shift_ext_in with
      (g := (fun j : nat =>
               infRobustness ψ τ (i - (S a) - j) ⊓ op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - S a - k))))
    by now intros; f_equal; f_equal; lia.
  change (infRobustness (FAnd (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) (FAlways 0 a ϕ)) τ i)
    with (infRobustness (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) τ i ⊓ infRobustness (FAlways 0 a ϕ) τ i).
  f_equal.
  rewrite fdelay_correctness.
  assert (S a <= i) by lia. rewrite <-Nat.leb_le in H0. rewrite H0. clear H0.
  auto.
Qed.

Lemma sinceDual_sometime_unbounded :
  forall (ϕ ψ : Formula A) τ a i,
    a < i ->
    infRobustness (FSinceDualUnbounded (S a) ϕ ψ) τ i
    = infRobustness (FOr (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) (FSometime 0 a ϕ)) τ i.
Proof.
  intros. simpl infRobustness at 1.
  unfold meet_b.
  replace (S a) with (1 + a) at 1 by lia.
  replace i with ((i - a) + a) at 1 by lia.
  rewrite <- op_b_shift_ext_in with
      (lo := 1)
      (hi := (i - a))
      (g := (fun j : nat => infRobustness ψ τ (i - a - j) ⊔ join_i 0 (j + a) (fun k : nat => infRobustness ϕ τ (i - k)))) by now intros; f_equal; f_equal; lia.
  under op_b_ext_in => j.
  intros.
  unfold join_i.
  replace (j + a) with (S a + (j - 1)) by lia.
  rewrite -> op_i_app with
      (l1 := S a)
      (l2 := (j - 1)).
  simpl.
  rewrite ->join_comm with (x := (op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)))).
  rewrite <-join_assoc.
  replace ( op_i Val 0 (S a) (fun k : nat => infRobustness ϕ τ (i - k)) )
    with
      (infRobustness (FSometime 0 a ϕ) τ i)
    by now simpl; unfold join_b; unfold op_b; f_equal; lia.
  over.
  replace (op_b Val 1 (i - a)
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
       ⊔ infRobustness (FSometime 0 a ϕ) τ i))
    with
      (meet_b 1 (i - a)
    (fun j : nat =>
     (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))
     ⊔ infRobustness (FSometime 0 a ϕ) τ i)) by auto.
  rewrite ->meet_b_distr_ext_in
  with (g := (fun j : nat =>
                (infRobustness ψ τ (i - a - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  (S a) (j - 1) (fun k : nat => infRobustness ϕ τ (i - k)))))
       (v := (infRobustness (FSometime 0 a ϕ) τ i)) by now intros; auto; lia.
  under meet_b_ext_in => j.
  intros.
  replace (S a) with (0 + S a) by lia.
  rewrite <- op_i_shift_ext_in with
      (f := (fun k : nat => infRobustness ϕ τ (i - k)))
      (g := (fun k : nat => infRobustness ϕ τ (i - (S a) - k)) )
  by now intros; f_equal; lia.
  over.
  replace 1 with (0 + 1) at 1 by lia.
  replace (i - a) with ((i - S a) + 1) by lia.
  unfold meet_b.
  rewrite <- op_b_shift_ext_in with
      (g := (fun j : nat =>
               infRobustness ψ τ (i - (S a) - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val) 0 j (fun k : nat => infRobustness ϕ τ (i - S a - k))))
    by now intros; f_equal; f_equal; lia.
  change (infRobustness (FOr (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) (FSometime 0 a ϕ)) τ i)
    with (infRobustness (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) τ i ⊔ infRobustness (FSometime 0 a ϕ) τ i).
  f_equal.
  rewrite fdelayDual_correctness.
  assert (S a <= i) by lia. rewrite <-Nat.leb_le in H0. rewrite H0. clear H0.
  auto.
Qed.

Lemma since_incremental :
  forall (ϕ ψ : Formula A) τ i,
    infRobustness (FSinceUnbounded 0 ϕ ψ) τ (S i)
    = ((infRobustness ψ τ (S i))
        ⊔ (infRobustness (FSinceUnbounded 0 ϕ ψ) τ i
          ⊓ infRobustness ϕ τ (S i))).
Proof.
  intros. remember (S i) as i0. simpl infRobustness at 1.
  unfold join_b. rewrite Heqi0.
  replace (S i) with (1 + i) at 1 by lia.
  rewrite ->op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. unfold op_i at 1.
  unfold meet_i at 1. unfold op_i.
  simpl finite_op.
  unfold finite_op at 1 2. simpl List.fold_left.
  rewrite join_bottom_l. rewrite meet_top_r.
  f_equal.
  replace 1 with (0 + 1) at 1 by lia.
  replace (1 + i) with (i + 1) by lia.
  rewrite <-op_b_shift_ext_in
    with
      (g := (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k))))
      (h := 1)
    by now intros; f_equal; f_equal; lia.
  replace ( (op_b Val 0 i
                  (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) )
    with ( (join_b 0 i
                   (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) ) by auto.
  under join_b_ext_in => j.
  intros.
  replace (S j) with (1 + j) at 1 by lia.
  unfold meet_i.
  rewrite ->op_i_app with (l1 := 1).
  unfold op_i at 1. simpl finite_op.
  unfold finite_op. simpl List.fold_left.
  rewrite meet_top_l.
  rewrite <-op_i_shift_ext with
      (g :=(fun k : nat => infRobustness ϕ τ (i - k)))
    by now intros; f_equal; lia.
  replace (op (infRobustness ϕ τ (S i)) (op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) )
    with
      ((op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) ⊓ (infRobustness ϕ τ (S i)))
    by now simpl; rewrite meet_comm.
  rewrite <- meet_assoc.
  over.
  rewrite ->join_b_distr_ext_in with
  (g := (fun j : nat =>
           (infRobustness ψ τ (i - j) ⊓ op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k)))))
  (v := infRobustness ϕ τ (S i)) by now auto; lia.
  auto.
Qed.

Lemma sinceDual_incremental :
  forall (ϕ ψ : Formula A) τ i,
    infRobustness (FSinceDualUnbounded 0 ϕ ψ) τ (S i)
    = ((infRobustness ψ τ (S i))
        ⊓ (infRobustness (FSinceDualUnbounded 0 ϕ ψ) τ i
          ⊔ infRobustness ϕ τ (S i))).
Proof.
  intros. remember (S i) as i0. simpl infRobustness at 1.
  unfold meet_b. rewrite Heqi0.
  replace (S i) with (1 + i) at 1 by lia.
  rewrite ->op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. unfold op_i at 1.
  unfold join_i at 1. unfold op_i.
  simpl finite_op.
  unfold finite_op at 1 2. simpl List.fold_left.
  rewrite meet_top_l. rewrite join_bottom_r.
  f_equal.
  replace 1 with (0 + 1) at 1 by lia.
  replace (1 + i) with (i + 1) by lia.
  rewrite <-op_b_shift_ext_in
    with
      (g := (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k))))
      (h := 1)
    by now intros; f_equal; f_equal; lia.
  replace ( (op_b Val 0 i
                  (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) )
    with ( (meet_b 0 i
                   (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) ) by auto.
  under meet_b_ext_in => j.
  intros.
  replace (S j) with (1 + j) at 1 by lia.
  unfold join_i.
  rewrite ->op_i_app with (l1 := 1).
  unfold op_i at 1. simpl finite_op.
  unfold finite_op. simpl List.fold_left.
  rewrite join_bottom_l.
  rewrite <-op_i_shift_ext with
      (g :=(fun k : nat => infRobustness ϕ τ (i - k)))
    by now intros; f_equal; lia.
  replace (op (infRobustness ϕ τ (S i)) (op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) )
    with
      ((@op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  0 j (fun k : nat => infRobustness ϕ τ (i - k))) ⊔ (infRobustness ϕ τ (S i)))
    by now simpl; rewrite join_comm.
  rewrite <- join_assoc.
  over.
  rewrite ->meet_b_distr_ext_in with
  (g := (fun j : nat =>
           (infRobustness ψ τ (i - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  0 j (fun k : nat => infRobustness ϕ τ (i - k)))))
  (v := infRobustness ϕ τ (S i)) by now auto; lia.
  auto.
Qed.

Lemma sometimeUnbounded_incremental :
  forall (ϕ : Formula A) τ i,
    infRobustness (FSometimeUnbounded 0 ϕ) τ (S i)
    = ((infRobustness (FSometimeUnbounded 0 ϕ) τ i) ⊔ (infRobustness ϕ τ (S i))).
Proof.
  intros.
  replace (infRobustness (FSometimeUnbounded 0 ϕ) τ (S i)) with
      (join_b 0 (S i) (fun j => (infRobustness ϕ τ ((S i) - j)))) by auto.
  unfold join_b. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto. unfold op_i.
  simpl finite_op. rewrite finite_op_singleton.
  replace 1 with (0 + 1) by lia. replace (S i) with (i + 1) by lia.
  rewrite <- op_b_shift.
  rewrite <- join_comm.
  enough
    ((@op_b Val joinMonoid 0 i (fun i0 : nat => infRobustness ϕ τ (i + 1 - (i0 + 1))))
     = infRobustness (FSometimeUnbounded 0 ϕ) τ i) by now rewrite H.
  under op_b_ext => i0. replace (i + 1 - (i0 + 1)) with (i - i0) by lia. over.
  auto.
Qed.

Lemma alwaysUnbounded_incremental :
  forall (ϕ : Formula A) τ i,
    infRobustness (FAlwaysUnbounded 0 ϕ) τ (S i)
    = ((infRobustness (FAlwaysUnbounded 0 ϕ) τ i) ⊓ (infRobustness ϕ τ (S i))).
Proof.
  intros.
  replace (infRobustness (FAlwaysUnbounded 0 ϕ) τ (S i)) with
      (meet_b 0 (S i) (fun j => (infRobustness ϕ τ ((S i) - j)))) by auto.
  unfold meet_b. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto. unfold op_i.
  simpl finite_op. rewrite finite_op_singleton.
  replace 1 with (0 + 1) by lia. replace (S i) with (i + 1) by lia.
  rewrite <- op_b_shift.
  rewrite <- meet_comm.
  enough
    ((@op_b Val meetMonoid 0 i (fun i0 : nat => infRobustness ϕ τ (i + 1 - (i0 + 1))))
     = infRobustness (FAlwaysUnbounded 0 ϕ) τ i) by now rewrite H.
  under op_b_ext => i0. replace (i + 1 - (i0 + 1)) with (i - i0) by lia. over.
  auto.
Qed.

Lemma sometimeBounded_incremental :
  forall (ϕ : Formula A) τ n i,
    infRobustness (FSometime 0 (S n) ϕ) τ (S i)
    = ((infRobustness (FSometime 0 n ϕ) τ i) ⊔ infRobustness ϕ τ (S i)).
Proof.
  intros.
  replace (infRobustness (FSometime 0 (S n) ϕ) τ (S i))
    with (join_b 0 (S (min i n)) (fun j : nat => infRobustness ϕ τ (S i - j))) by auto.
  simpl infRobustness at 2.
  unfold join_b at 1. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto.
  unfold op_i. simpl List.map. rewrite finite_op_singleton.
  rewrite join_comm.
  replace 1 with (0 + 1) by lia. replace (S (min i n)) with (min i n + 1) by lia.
  rewrite <- op_b_shift_ext with (h := 1) (g := (fun j : nat => infRobustness ϕ τ ( i - j))).
  auto.
  intros. f_equal. lia.
Qed.

Lemma alwaysBounded_incremental :
  forall (ϕ : Formula A) τ n i,
    infRobustness (FAlways 0 (S n) ϕ) τ (S i)
    = ((infRobustness (FAlways 0 n ϕ) τ i) ⊓ infRobustness ϕ τ (S i)).
Proof.
  intros.
  replace (infRobustness (FAlways 0 (S n) ϕ) τ (S i))
    with (meet_b 0 (S (min i n)) (fun j : nat => infRobustness ϕ τ (S i - j))) by auto.
  simpl infRobustness at 2.
  unfold meet_b at 1. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto.
  unfold op_i. simpl List.map. rewrite finite_op_singleton.
  rewrite meet_comm.
  replace 1 with (0 + 1) by lia. replace (S (min i n)) with (min i n + 1) by lia.
  rewrite <- op_b_shift_ext with (h := 1) (g := (fun j : nat => infRobustness ϕ τ ( i - j))).
  auto.
  intros. f_equal. lia.
Qed.


End InfRobustness.

Arguments infRobustness {Val A lattice_val boundedLattice_val}.

