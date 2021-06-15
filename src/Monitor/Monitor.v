(**

This file contains:

1. Defintion of a Monitor
  - a monitor is defined as a Mealy machine whose values are in some bounded distributive lattice.
2. What it means to say that a monitor m [implements] a formula ϕ.
3. A number of Mealy Combinators that act a certain way on Monitors.
  - These corresponds to the main building blocks in our construction.
  - We prove that each of the corresponding combinators are also correct.

*)

Require Import Coq.Lists.List.

From Algebra Require Import Monoid.
From Algebra Require Import Lattice.
From Syntax Require Import Formula.
From Semantics Require Import Robustness.
From Semantics Require Import InfRobustness.
From NonEmptyList Require Import NonEmptyList.
Require Import Mealy.
Require Import Queue.
Require Import AggQueue.
From Lemmas Require Import Lemmas.

Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Section Monitor.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Monitor : Type := Mealy A Val.

Definition implements (m : Monitor) (ϕ : Formula A) : Prop :=
  forall σ,
    gOut m σ = robustness ϕ σ.

Definition monAtomic (f : A -> Val) : Monitor :=
  mLift f.

Lemma monAtomic_correctness :
  forall f, implements (monAtomic f) (FAtomic f).
Proof.
  intros. unfold implements. intros.
  unfold monAtomic. rewrite mLift_result.
  unfold robustness. simpl. f_equal.
  unfold extend.
  rewrite rev_nth. assert ((length (toList σ)) >= 1) by apply length_toList1.
  replace ((length (toList σ) - S (Nat.pred (length (toList σ))))) with 0 by lia.
  now rewrite nth_latest.
  assert (length (toList σ) >= 1) by apply length_toList1. lia.
Qed.

Definition monAnd (m n : Monitor) : Monitor :=
  mBinOp meet m n.

Lemma monAnd_correctness m1 m2 ϕ1 ϕ2 :
  implements m1 ϕ1
  -> implements m2 ϕ2
  -> implements (monAnd m1 m2) (FAnd ϕ1 ϕ2).
Proof.
  unfold implements.
  unfold monAnd.
  intros. rewrite mBinOp_result.
  unfold robustness in *. simpl in *.
  rewrite H. rewrite H0. auto.
Qed.


Definition monOr (m n : Monitor) : Monitor :=
  mBinOp join m n.

Lemma monOr_correctness m1 m2 ϕ1 ϕ2 :
  implements m1 ϕ1
  -> implements m2 ϕ2
  -> implements (monOr m1 m2) (FOr ϕ1 ϕ2).
Proof.
  unfold implements.
  unfold monOr.
  intros. rewrite mBinOp_result.
  unfold robustness in *. simpl in *.
  rewrite H. rewrite H0. auto.
Qed.

Definition monSometimeUnbounded (m : Monitor) : Monitor :=
  mFold join m bottom.

Lemma monSometimeUnbounded_correctness m ϕ :
  implements m ϕ
  -> implements (monSometimeUnbounded m) (FSometimeUnbounded 0 ϕ).
Proof.
  unfold implements. unfold monSometimeUnbounded.
  intros. rewrite mFold_result.
  induction σ.
  - simpl. rewrite join_bottom_l.
    specialize (H (singleton a)). simpl in H. rewrite H.
    unfold robustness. simpl. unfold join_b. unfold Monoid.op_b.
    unfold Monoid.op_i. simpl. now rewrite Monoid.finite_op_singleton.
  - simpl gCollect. simpl toList. simpl rev.
    rewrite fold_left_app. rewrite IHσ.
    simpl fold_left.
    replace (mOut (gNext m σ) a) with (gOut m (snocNE σ a)) by auto.
    rewrite H. remember (snocNE σ a) as σ'.
    unfold robustness at 3. remember (Nat.pred (length (toList σ'))).
    destruct n. subst σ'. simpl in Heqn. pose proof (length_toList1 σ). lia.
    rewrite sometimeUnbounded_incremental. unfold robustness.
    rewrite <- Heqn. rewrite Heqσ' in Heqn. simpl in Heqn.
    rewrite <- Heqn. simpl pred. f_equal. apply infRobustness_prefix.
    subst σ'. unfold extend. simpl. intros. rewrite app_nth1.
    apply nth_indep. rewrite rev_length. lia.
    rewrite rev_length. lia.
Qed.

Definition monAlwaysUnbounded (m : Monitor) : Monitor :=
  mFold meet m top.

Lemma monAlwaysUnbounded_correctness m ϕ :
  implements m ϕ
  -> implements (monAlwaysUnbounded m) (FAlwaysUnbounded 0 ϕ).
Proof.
  unfold implements. unfold monAlwaysUnbounded.
  intros. rewrite mFold_result.
  induction σ.
  - simpl. rewrite meet_top_l.
    specialize (H (singleton a)). simpl in H. rewrite H.
    unfold robustness. simpl. unfold meet_b. unfold Monoid.op_b.
    unfold Monoid.op_i. simpl. now rewrite Monoid.finite_op_singleton.
  - simpl gCollect. simpl toList. simpl rev.
    rewrite fold_left_app. rewrite IHσ.
    simpl fold_left.
    replace (mOut (gNext m σ) a) with (gOut m (snocNE σ a)) by auto.
    rewrite H. remember (snocNE σ a) as σ'.
    unfold robustness at 3. remember (Nat.pred (length (toList σ'))).
    destruct n. subst σ'. simpl in Heqn. pose proof (length_toList1 σ). lia.
    rewrite alwaysUnbounded_incremental. unfold robustness.
    rewrite <- Heqn. rewrite Heqσ' in Heqn. simpl in Heqn.
    rewrite <- Heqn. simpl pred. f_equal. apply infRobustness_prefix.
    subst σ'. unfold extend. simpl. intros. rewrite app_nth1.
    apply nth_indep. rewrite rev_length. lia.
    rewrite rev_length. lia.
Qed.

Lemma nth_gCollect m n ϕ :
  implements m ϕ
  -> forall σ, n < (length (toList σ))
         -> forall d, nth n (toList (gCollect m σ)) d
                            = infRobustness ϕ (extend σ) ((Nat.pred (length (toList σ))) - n).
Proof.
  intros.
  generalize dependent σ. generalize dependent n. induction n.
    + intros. replace (Nat.pred (length (toList σ)) - 0) with (Nat.pred (length (toList σ))) by lia.
      replace (infRobustness ϕ (extend σ) (Nat.pred (length (toList σ))))
        with (robustness ϕ σ) by auto.
      rewrite nth_latest. rewrite <- gCollect_gOut. now rewrite H.
    + intros. destruct σ.
      ++ simpl in H0. lia.
      ++ simpl gCollect. simpl toList. simpl nth. rewrite IHn by now simpl in H0; lia.
         simpl length.
         replace  (Nat.pred (S (length (toList σ))) - S n)
           with (Nat.pred ((length (toList σ))) -  n) by lia.
         apply infRobustness_prefix. intros.
         simpl in H0. unfold extend.
         simpl. rewrite app_nth1 by now rewrite rev_length; lia.
         apply nth_indep. rewrite rev_length. lia.
Qed.

Lemma extend_gCollect m n ϕ :
  implements m ϕ
  -> forall σ, n < (length (toList σ))
               -> extend (gCollect m σ) n
                 = infRobustness ϕ (extend σ) n.
Proof.
  intros. unfold extend at 1.
  rewrite rev_nth.
  {
    rewrite nth_gCollect with (ϕ := ϕ).
    { f_equal.
      replace (length (toList (gCollect m σ)))
        with (neLength (gCollect m σ)) by now rewrite length_toList.
      rewrite gCollect_neLength. rewrite <- length_toList.
      lia.
    }
    { auto. }
   {
    rewrite length_toList. rewrite gCollect_neLength.
    rewrite <- length_toList. lia.
   }
  }
  { rewrite length_toList. rewrite gCollect_neLength.
    rewrite <- length_toList. auto. }
Qed.




Definition monDelay (n : nat) (m : Monitor) : Monitor :=
  delay bottom n m.

Lemma monDelay_correctness m n ϕ :
  implements m ϕ
  -> implements (monDelay n m) (FDelay n ϕ).
Proof.
  unfold implements.
  unfold monDelay. intros.
  rewrite delay_result. unfold robustness. rewrite fdelay_correctness.
  fold (@robustness Val A lattice_val boundedLattice_val ϕ).
  destruct (Compare_dec.dec_le n (Nat.pred (length (toList σ)))).
  - rewrite Compare_dec.leb_correct by assumption.
    apply nth_gCollect. unfold implements. apply H.
    pose proof (length_toList1 σ). lia.
  - rewrite Compare_dec.leb_correct_conv by lia.
    rewrite nth_overflow. auto.
    rewrite length_toList. rewrite gCollect_neLength.
    rewrite length_toList in H0. lia.
Qed.

Definition monDelayDual (n : nat) (m : Monitor) : Monitor :=
  delay top n m.

Lemma monDelayDual_correctness m n ϕ :
  implements m ϕ
  -> implements (monDelayDual n m) (FDelayDual n ϕ).
Proof.
  unfold implements.
  unfold monDelayDual. intros.
  rewrite delay_result. unfold robustness. rewrite fdelayDual_correctness.
  fold (@robustness Val A lattice_val boundedLattice_val ϕ).
  destruct (Compare_dec.dec_le n (Nat.pred (length (toList σ)))).
  - rewrite Compare_dec.leb_correct by assumption.
    apply nth_gCollect. unfold implements. apply H.
    pose proof (length_toList1 σ). lia.
  - rewrite Compare_dec.leb_correct_conv by lia.
    rewrite nth_overflow. auto.
    rewrite length_toList. rewrite gCollect_neLength.
    rewrite length_toList in H0. lia.
Qed.

Definition monSometimeBounded (n : nat) (m : Monitor) : Monitor :=
  @mFoldWin _ joinMonoid _ (S n) m.

Lemma monSometimeBounded_correctness m n ϕ :
  implements m ϕ
  -> implements (monSometimeBounded n m) (FSometime 0 n ϕ).
Proof.
  unfold implements. intros.
  unfold monSometimeBounded. rewrite mWinFold_result.
  revert n. induction σ.
  - unfold robustness. simpl. unfold join_b. unfold Monoid.op_b. unfold Monoid.op_i.
    simpl. intros. rewrite lastn_all2. repeat rewrite Monoid.finite_op_singleton.
    specialize (H (singleton a)). simpl in H. rewrite H. auto.
    simpl. lia.
  - simpl gCollect. simpl toList. simpl rev. intros.
    rewrite lastn_last. rewrite <- finite_op_app. rewrite finite_op_singleton.
    specialize (H (snocNE σ a)). simpl in H.
    rewrite H.
    destruct n.
    + rewrite lastn_0. simpl. unfold finite_op. simpl.
      rewrite join_bottom_l.
      unfold robustness.
      replace (FSometime 0 0 ϕ) with (FDelay 0 ϕ) by auto. rewrite fdelay_correctness.
      simpl. now rewrite <- Minus.minus_n_O.
    + rewrite IHσ. unfold robustness.
      simpl pred at 3. pose proof (length_toList1 σ).
      remember (length (toList σ)). destruct n0.  lia.
      rewrite sometimeBounded_incremental. simpl pred.
      rewrite <- Heqn0.
      enough ((infRobustness (FSometime 0 n ϕ) (extend σ) n0)
              = (infRobustness (FSometime 0 n ϕ) (extend (snocNE σ a)) n0)).
      now rewrite H1.
      apply extends_infRobustness with (σ := σ). apply extend_extends.
      unfold extends. unfold extend. intros. simpl.
      rewrite app_nth1. rewrite nth_error_nth' with (d := a).
      auto.
      rewrite rev_length. auto.
      rewrite rev_length. auto.
      lia.
Qed.

Definition monAlwaysBounded (n : nat) (m : Monitor) : Monitor :=
  @mFoldWin _ meetMonoid _ (S n) m.

Lemma monAlwaysBounded_correctness m n ϕ :
  implements m ϕ
  -> implements (monAlwaysBounded n m) (FAlways 0 n ϕ).
Proof.
  unfold implements. intros.
  unfold monAlwaysBounded. rewrite mWinFold_result.
  revert n. induction σ.
  - unfold robustness. simpl. unfold meet_b. unfold Monoid.op_b. unfold Monoid.op_i.
    simpl. intros. rewrite lastn_all2. repeat rewrite Monoid.finite_op_singleton.
    specialize (H (singleton a)). simpl in H. rewrite H. auto.
    simpl. lia.
  - simpl gCollect. simpl toList. simpl rev. intros.
    rewrite lastn_last. rewrite <- finite_op_app. rewrite finite_op_singleton.
    specialize (H (snocNE σ a)). simpl in H.
    rewrite H.
    destruct n.
    + rewrite lastn_0. simpl. unfold finite_op. simpl.
      rewrite meet_top_l.
      unfold robustness.
      replace (FAlways 0 0 ϕ) with (FDelayDual 0 ϕ) by auto. rewrite fdelayDual_correctness.
      simpl. now rewrite <- Minus.minus_n_O.
    + rewrite IHσ. unfold robustness.
      simpl pred at 3. pose proof (length_toList1 σ).
      remember (length (toList σ)). destruct n0.  lia.
      rewrite alwaysBounded_incremental. simpl pred.
      rewrite <- Heqn0.
      enough ((infRobustness (FAlways 0 n ϕ) (extend σ) n0)
              = (infRobustness (FAlways 0 n ϕ) (extend (snocNE σ a)) n0)).
      now rewrite H1.
      apply extends_infRobustness with (σ := σ). apply extend_extends.
      unfold extends. unfold extend. intros. simpl.
      rewrite app_nth1. rewrite nth_error_nth' with (d := a).
      auto.
      rewrite rev_length. auto.
      rewrite rev_length. auto.
      lia.
Qed.

CoFixpoint sinceAux (m1 m2 : Monitor) (pre : Val) : Monitor :=
  {| mOut (a : A) :=  (mOut m2 a) ⊔ (pre ⊓ (mOut m1 a));
     mNext (a : A) := sinceAux (mNext m1 a) (mNext m2 a) ( (mOut m2 a) ⊔ (pre ⊓ (mOut m1 a)))
  |}.

Definition monSince (m1 m2 : Monitor) : Monitor :=
  sinceAux m1 m2 bottom.

Lemma monSince_state (m n : Monitor) (σ : nonEmpty A) :
  gNext (monSince m n) σ
  = sinceAux (gNext m σ) (gNext n σ)
             (gOut (monSince m n) σ).
Proof.
  induction σ.
  - auto.
  - simpl. rewrite IHσ. auto.
Qed.

Lemma monSince_correctness (m n : Monitor) (ϕ ψ : Formula A) :
  implements m ϕ
  -> implements n ψ
  -> implements (monSince m n) (FSinceUnbounded 0 ϕ ψ).
Proof.
  unfold implements. intros. induction σ.
  - simpl. rewrite meet_bottom_l. rewrite join_bottom_r.
    unfold robustness. simpl. unfold join_b. unfold op_b. simpl.
    unfold op_i. simpl. rewrite finite_op_singleton.
    unfold meet_i. unfold op_i. simpl. unfold finite_op. simpl.
    rewrite meet_top_r. unfold extend. simpl.
    specialize (H0 (singleton a)). simpl in H0.
    rewrite H0. auto.
  - simpl. rewrite monSince_state. simpl. rewrite IHσ.
    specialize (H (snocNE σ a)). specialize (H0 (snocNE σ a)).
    simpl in H, H0. rewrite H, H0. unfold robustness.
    simpl pred. remember (length (toList σ)). pose proof (length_toList1 σ).
    destruct n0. lia.
    simpl pred. rewrite since_incremental by assumption.
    f_equal. f_equal. apply infRobustness_prefix. intros. unfold extend.
    simpl. rewrite app_nth1. apply nth_indep.
    rewrite rev_length. lia.
    rewrite rev_length. lia.
Qed.

CoFixpoint sinceDualAux (m1 m2 : Monitor) (pre : Val) : Monitor :=
  {| mOut (a : A) :=  (mOut m2 a) ⊓ (pre ⊔ (mOut m1 a));
     mNext (a : A) := sinceDualAux (mNext m1 a) (mNext m2 a) ( (mOut m2 a) ⊓ (pre ⊔ (mOut m1 a)))
  |}.

Definition monSinceDual (m1 m2 : Monitor) : Monitor :=
  sinceDualAux m1 m2 top.

Lemma monSinceDual_state (m n : Monitor) (σ : nonEmpty A) :
  gNext (monSinceDual m n) σ
  = sinceDualAux (gNext m σ) (gNext n σ)
             (gOut (monSinceDual m n) σ).
Proof.
  induction σ.
  - auto.
  - simpl. rewrite IHσ. auto.
Qed.

Lemma monSinceDual_correctness (m n : Monitor) (ϕ ψ : Formula A) :
  implements m ϕ
  -> implements n ψ
  -> implements (monSinceDual m n) (FSinceDualUnbounded 0 ϕ ψ).
Proof.
  unfold implements. intros. induction σ.
  - simpl. rewrite join_top_l. rewrite meet_top_r.
    unfold robustness. simpl. unfold meet_b. unfold op_b. simpl.
    unfold op_i. simpl. rewrite finite_op_singleton.
    unfold join_i. unfold op_i. simpl. unfold finite_op. simpl.
    rewrite join_bottom_r. unfold extend. simpl.
    specialize (H0 (singleton a)). simpl in H0.
    rewrite H0. auto.
  - simpl. rewrite monSinceDual_state. simpl. rewrite IHσ.
    specialize (H (snocNE σ a)). specialize (H0 (snocNE σ a)).
    simpl in H, H0. rewrite H, H0. unfold robustness.
    simpl pred. remember (length (toList σ)). pose proof (length_toList1 σ).
    destruct n0. lia.
    simpl pred. rewrite sinceDual_incremental by assumption.
    f_equal. f_equal. apply infRobustness_prefix. intros. unfold extend.
    simpl. rewrite app_nth1. apply nth_indep.
    rewrite rev_length. lia.
    rewrite rev_length. lia.
Qed.

End Monitor.


Arguments Monitor {Val A}.
Arguments implements {Val A lattice_val boundedLattice_val}.
Arguments monAtomic {Val A}.
Arguments monAnd {Val A lattice_val}.
Arguments monOr {Val A lattice_val}.
Arguments monSometimeUnbounded {Val A lattice_val boundedLattice_val}.
Arguments monAlwaysUnbounded {Val A lattice_val boundedLattice_val}.
Arguments monDelay {Val A lattice_val boundedLattice_val}.
Arguments monDelayDual {Val A lattice_val boundedLattice_val}.
Arguments monSometimeBounded {Val A lattice_val boundedLattice_val}.
Arguments monAlwaysBounded {Val A lattice_val boundedLattice_val}.
Arguments monSince {Val A lattice_val boundedLattice_val}.
Arguments monSinceDual {Val A lattice_val boundedLattice_val}.
