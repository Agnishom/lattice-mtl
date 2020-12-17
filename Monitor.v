Require Import Coq.Lists.List.

Require Import Lattice.
Require Import Formula.
Require Import Robustness.
Require Import InfRobustness.
Require Import NonEmptyList.
Require Import Mealy.

Require Import Lia.

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
  -> forall σ, n < length (toList σ)
  -> forall d, nth n (toList (gCollect m σ)) d = infRobustness ϕ (extend σ) (pred (length (toList σ)) - n).
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
  @mFoldWin _ joinMonoid _ n m.

Lemma monSometimeBounded_correctness m n ϕ :
  implements m ϕ
  -> implements (monSometimeBounded n m) (FSometime 0 n ϕ).
Proof.
  unfold implements. intros.
  unfold monSometimeBounded. rewrite mWinFold_result.
  unfold robustness. simpl.
Admitted.

End Monitor.


