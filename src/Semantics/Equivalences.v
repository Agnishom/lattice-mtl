(**

This file contains several claims of equivalence between temporal logic formulas.
These properties are necessary so that any formula can be converted to what we call a normal form. (See [../Syntax/Normal.v])

*)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.

Require Import InfRobustness.
Require Import SimpleProperties.

Section Equivalences.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.



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
  forall (ϕ : Formula A) lo,
    equivalent (FSometimeUnbounded lo ϕ) (FDelay lo (FSometimeUnbounded 0 ϕ)).
Proof.
  unfold equivalent.
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
  forall (ϕ : Formula A) lo,
    equivalent (FAlwaysUnbounded lo ϕ) (FDelayDual lo (FAlwaysUnbounded 0 ϕ)).
Proof.
  unfold equivalent.
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

Lemma since_always_bounded1 :
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

Lemma since_always_bounded :
  forall (ϕ ψ : Formula A) a b,
    a < b ->
    equivalent (FSince (S a) b ϕ ψ)
               (FAnd (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) (FAlways 0 a ϕ)).
Proof.
  unfold equivalent.
  intros.
  destruct (Compare_dec.dec_lt a i).
    + now apply since_always_bounded1.
    + assert (S a > i) by lia.
      rewrite fSince_i_lo. apply H1.
      replace (infRobustness (FAnd (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) (FAlways 0 a ϕ)) τ i)
        with ((infRobustness (FDelay (S a) (FSince 0 (b - S a) ϕ ψ)) τ i) ⊓ (infRobustness (FAlways 0 a ϕ) τ i)) by auto.
      rewrite fdelay_correctness. rewrite -> Compare_dec.leb_correct_conv by lia.
      now rewrite meet_bottom_l.
Qed.

Lemma sinceDual_sometime_bounded1 :
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

Lemma sinceDual_sometime_bounded :
  forall (ϕ ψ : Formula A) τ a b i,
    a < b ->
    infRobustness (FSinceDual (S a) b ϕ ψ) τ i
    = infRobustness (FOr (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) (FSometime 0 a ϕ)) τ i.
Proof.
  intros.
  destruct (Compare_dec.dec_lt a i).
    + now apply sinceDual_sometime_bounded1.
    + assert (S a > i) by lia.
      rewrite fSinceDual_i_lo. apply H1.
      replace (infRobustness (FOr (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) (FSometime 0 a ϕ)) τ i)
        with ((infRobustness (FDelayDual (S a) (FSinceDual 0 (b - S a) ϕ ψ)) τ i) ⊔ (infRobustness (FSometime 0 a ϕ) τ i)) by auto.
      rewrite fdelayDual_correctness. rewrite -> Compare_dec.leb_correct_conv by lia.
      now rewrite join_top_l.
Qed.

Lemma since_always_unbounded1 :
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

Lemma since_always_unbounded :
  forall (ϕ ψ : Formula A) a,
    equivalent
      (FSinceUnbounded (S a) ϕ ψ)
      (FAnd (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) (FAlways 0 a ϕ)).
Proof.
  unfold equivalent. intros.
  destruct (Compare_dec.dec_lt a i).
  - now apply since_always_unbounded1.
  - assert (S a > i) by lia.
    rewrite fSinceUnbounded_i_lo. apply H0.
    replace (infRobustness (FAnd (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) (FAlways 0 a ϕ)) τ i)
      with ((infRobustness (FDelay (S a) (FSinceUnbounded 0 ϕ ψ)) τ i) ⊓ (infRobustness (FAlways 0 a ϕ) τ i)) by auto.
    rewrite fdelay_correctness. rewrite -> Compare_dec.leb_correct_conv by lia.
    now rewrite meet_bottom_l.
Qed.

Lemma sinceDual_sometime_unbounded1 :
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

Lemma sinceDual_sometime_unbounded :
  forall (ϕ ψ : Formula A) a,
    equivalent
      (FSinceDualUnbounded (S a) ϕ ψ)
      (FOr (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) (FSometime 0 a ϕ)).
Proof.
  unfold equivalent. intros.
  destruct (Compare_dec.dec_lt a i).
  - now apply sinceDual_sometime_unbounded1.
  - assert (S a > i) by lia.
    rewrite fSinceDualUnbounded_i_lo. apply H0.
    replace (infRobustness (FOr (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) (FSometime 0 a ϕ)) τ i)
      with ((infRobustness (FDelayDual (S a) (FSinceDualUnbounded 0 ϕ ψ)) τ i) ⊔ (infRobustness (FSometime 0 a ϕ) τ i)) by auto.
    rewrite fdelayDual_correctness. rewrite -> Compare_dec.leb_correct_conv by lia.
    now rewrite join_top_l.
Qed.

End Equivalences.
