From Hammer Require Import Hammer.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Require Import Lattice.
Require Import Formula.
Require Import MTLTactics.
Require Import Moore.
Require Import Monoid.

Import ListNotations.

Generalizable All Variables.

Variable (Val : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Arguments robustness {Val lattice_val boundedLattice_val A}.
Arguments Formula {Val A}.

Definition Monitor (A : Type) : Type := Moore A Val.

(* What it means for a monitor to implement a formula *)

Definition implements {A : Type} (m : Monitor A) (f : Formula) : Prop :=
  forall l,
    gFinal m l = robustness f l.

(* this simply evaluates f on the latest item *)

Definition monLift {A : Type} (f : A -> Val) : Monitor A :=
  mLift f bottom.

Lemma monLift_correctness {A : Type} (f : A -> Val):
  implements (monLift f) (FAtomic Val f).
Proof.
  unfold monLift. unfold implements.
  intros. remember l. destruct l using list_r_ind.
  + unfold gFinal. Reconstr.scrush.
  + clear IHl. rewrite Heql0. rewrite mLift_correctness_final.
    simpl robustness. destruct (l ++ [x]) eqn:E. Reconstr.scrush.
    rewrite <- E. now rewrite last_nonempty.
Qed.

(* Pre combinator *)

Definition mDelay {A : Type} (n : nat) (m : Monitor A) : Monitor A :=
  delayyWith bottom (repeat' bottom n) [] m.

Definition mDelayDual {A : Type} (n : nat) (m : Monitor A) : Monitor A :=
  delayyWith top (repeat' top n) [] m.

Lemma mDelay_correctness {A : Type} (n : nat) (f : Formula) (m : Monitor A) :
  implements m f
  -> implements (mDelay n m) (FDelay Val n f).
Proof.
  unfold implements.
  intros. unfold mDelay.
  destruct l using list_r_ind.
  - now unfold gFinal.
  - rewrite repeat_repeat' in *.
    clear IHl. rewrite delayyWith_final with (d := bottom).
    simpl rev. rewrite app_nil_r.
    replace ([bottom] ++ repeat bottom n) with (repeat bottom (S n)) by auto.
    rewrite repeat_length.
    destruct (PeanoNat.Nat.le_gt_cases (S n) (length (l ++ [x])))
    ;replace (robustness (FDelay Val n f) (l ++ [x])) with
        (if ((S n) <=? length (l ++ [x]))
         then robustness f (firstn (length (l ++ [x]) - S n) (l ++ [x]))
         else bottom) by auto.
    + assert (H1 := H0). rewrite <- Nat.leb_le in H1.
    rewrite H1. clear H1.
    rewrite <- H. rewrite lastn_app.
    rewrite gCollect_length. rewrite app_length in H0. simpl in H0.
    replace (S n - S (length l)) with 0 by lia. simpl.
    rewrite <- gCollect_firstn_last with (d := bottom).
    rewrite hd_lastn_last_firstn.
    rewrite gCollect_length. rewrite app_length.
    replace ((length l + length [x] - S n)) with (S (length l) - S n) by now simpl; lia.
    rewrite gCollect_last. rewrite firstn_app.
    rewrite gCollect_length.
    replace ((S (S (length l) - S n) - S (length l))) with 0 by lia.
    simpl firstn. now rewrite app_nil_r.
    rewrite gCollect_length. lia.
    + assert (H1 := H0). rewrite <- Compare_dec.leb_iff_conv in H1.
      rewrite H1. clear H1.
      rewrite lastn_app. rewrite gCollect_length.
      destruct (S n - S (length l)) eqn:E.
      rewrite app_length in H0. simpl in H0. lia.
      rewrite lastn_repeat.
      replace (Init.Nat.min (S n0) (S n)) with (S (Init.Nat.min n0 n)) by lia.
      reflexivity.
Qed.

Lemma mDelayDual_correctness {A : Type} (n : nat) (f : Formula) (m : Monitor A) :
  implements m f
  -> implements (mDelayDual n m) (FDelayDual Val n f).
Proof.
  unfold implements.
  intros. unfold mDelayDual.
  destruct l using list_r_ind.
  - now unfold gFinal.
  - rewrite repeat_repeat' in *.
    clear IHl. rewrite delayyWith_final with (d := top).
    simpl rev. rewrite app_nil_r.
    replace ([top] ++ repeat top n) with (repeat top (S n)) by auto.
    rewrite repeat_length.
    destruct (PeanoNat.Nat.le_gt_cases (S n) (length (l ++ [x])))
    ;replace (robustness (FDelayDual Val n f) (l ++ [x])) with
        (if ((S n) <=? length (l ++ [x]))
         then robustness f (firstn (length (l ++ [x]) - S n) (l ++ [x]))
         else top) by auto.
    + assert (H1 := H0). rewrite <- Nat.leb_le in H1.
    rewrite H1. clear H1.
    rewrite <- H. rewrite lastn_app.
    rewrite gCollect_length. rewrite app_length in H0. simpl in H0.
    replace (S n - S (length l)) with 0 by lia. simpl.
    rewrite <- gCollect_firstn_last with (d := top).
    rewrite hd_lastn_last_firstn.
    rewrite gCollect_length. rewrite app_length.
    replace ((length l + length [x] - S n)) with (S (length l) - S n) by now simpl; lia.
    rewrite gCollect_last. rewrite firstn_app.
    rewrite gCollect_length.
    replace ((S (S (length l) - S n) - S (length l))) with 0 by lia.
    simpl firstn. now rewrite app_nil_r.
    rewrite gCollect_length. lia.
    + assert (H1 := H0). rewrite <- Compare_dec.leb_iff_conv in H1.
      rewrite H1. clear H1.
      rewrite lastn_app. rewrite gCollect_length.
      destruct (S n - S (length l)) eqn:E.
      rewrite app_length in H0. simpl in H0. lia.
      rewrite lastn_repeat.
      replace (Init.Nat.min (S n0) (S n)) with (S (Init.Nat.min n0 n)) by lia.
      reflexivity.
Qed.


(* Pointwise Binary Operations *)

Definition mAnd {A : Type} (m1 : Monitor A) (m2 : Monitor A) : Monitor A :=
  mBinOp meet m1 m2.

Definition mOr {A : Type} (m1 : Monitor A) (m2 : Monitor A) : Monitor A :=
  mBinOp join m1 m2.

Lemma mAnd_correctness {A : Type} (m1 m2 : Monitor A) (f1 f2 : Formula):
  implements m1 f1
  -> implements m2 f2
  -> implements (mAnd m1 m2) (FAnd Val f1 f2).
Proof.
  unfold implements. unfold mAnd. intros. rewrite mBinOp_final.
  Reconstr.scrush.
Qed.

Lemma mOr_correctness {A : Type} (m1 m2 : Monitor A) (f1 f2 : Formula):
  implements m1 f1
  -> implements m2 f2
  -> implements (mOr m1 m2) (FOr Val f1 f2).
Proof.
  unfold implements. unfold mOr. intros. rewrite mBinOp_final.
  Reconstr.scrush.
Qed.

(* Sometime and Always *)

Definition mSometime {A : Type} (m : Monitor A) : Monitor A :=
  @mFold Val joinMonoid A m.

Lemma sometime_correctness {A : Type} (m : Monitor A) (f : Formula) :
  implements m f
  -> implements (mSometime m) (FSometime Val f).
Proof.
  unfold mSometime. unfold implements. intros.
  rewrite mFold_final.
  simpl robustness. unfold finite_join.
  rewrite gCollect_prefixes. rewrite map_ext with (f := (gFinal m)) (g := (robustness f)).
  auto. auto.
Qed.

Definition mAlways {A : Type} (m : Monitor A) : Monitor A :=
  @mFold Val meetMonoid A m.

Lemma always_correctness {A : Type} (m : Monitor A) (f : Formula) :
  implements m f
  -> implements (mAlways m) (FAlways Val f).
Proof.
  unfold mAlways. unfold implements. intros.
  rewrite mFold_final.
  simpl robustness. unfold finite_join.
  rewrite gCollect_prefixes. rewrite map_ext with (f := (gFinal m)) (g := (robustness f)).
  auto. auto.
Qed.

(* Since *)

(* Represents m1 Since m2 : m2 has happened before and m1 has been happening since *)
CoFixpoint sinceAux { A : Type } (m1 m2 : Monitor A) (pre : Val) : Monitor A :=
  {| mOut := pre;
     mNext (a : A) := sinceAux (mNext m1 a) (mNext m2 a) ((mNextOut m2 a) ⊔ ((mNextOut m1 a) ⊓ pre))
  |}.

Definition since {A : Type} (m1 m2 : Monitor A) := sinceAux m1 m2 (mOut m2).

Lemma since_state {A : Type} (m1 m2 : Monitor A) (xs : list A) (x : A) :
  gNext (since m1 m2) (xs ++ [x]) =
  sinceAux (gNext m1 (xs ++ [x])) (gNext m2 (xs ++ [x]))
           (gFinal m2 (xs ++ [x]) ⊔ ((gFinal m1 (xs ++ [x])) ⊓ (gFinal (since m1 m2) xs))).
Proof.
  generalize dependent x. induction xs using list_r_ind.
  + simpl. Reconstr.scrush.
  + intros. rewrite gNext_app. rewrite IHxs. unfold gFinal. rewrite IHxs.
    unfold mNextOut. unfold gFinal. repeat rewrite gNext_app.
    simpl. Reconstr.scrush.
Qed.

Lemma since_final {A : Type} (m1 m2 : Monitor A) (xs : list A) (x : A) :
  gFinal (since m1 m2) (xs ++ [x]) = (gFinal m2 (xs ++ [x]) ⊔ ((gFinal m1 (xs ++ [x])) ⊓ (gFinal (since m1 m2) xs))).
Proof.
  pose proof (@since_state A m1 m2 xs x). unfold gFinal. Reconstr.scrush.
Qed.

Lemma since_correctness {A : Type} (f1 f2 : Formula) (m1 m2 : Monitor A):
  implements m1 f1
  -> implements m2 f2
  -> implements (since m1 m2) (FSince Val f1 f2).
Proof.
  unfold implements. intros.
  induction l using list_r_ind.
  - simpl. unfold gFinal. unfold finite_join. simpl. unfold finite_meet.
    simpl. rewrite meet_top_r. rewrite join_bottom_l. now rewrite <- H0.
  - rewrite since_inductive by exact distributiveLattice_val.
    rewrite since_final.
    rewrite IHl. rewrite H. rewrite H0.
    rewrite join_comm. now rewrite meet_comm.
Qed.

CoFixpoint sinceDualAux { A : Type } (m1 m2 : Monitor A) (pre : Val) : Monitor A :=
  {| mOut := pre;
     mNext (a : A) := sinceDualAux (mNext m1 a) (mNext m2 a) ((mNextOut m2 a) ⊓ ((mNextOut m1 a) ⊔ pre))
  |}.

Definition sinceDual {A : Type} (m1 m2 : Monitor A) := sinceDualAux m1 m2 (mOut m2).

Lemma sinceDual_state {A : Type} (m1 m2 : Monitor A) (xs : list A) (x : A) :
  gNext (sinceDual m1 m2) (xs ++ [x]) =
  sinceDualAux (gNext m1 (xs ++ [x])) (gNext m2 (xs ++ [x]))
           (gFinal m2 (xs ++ [x]) ⊓ ((gFinal m1 (xs ++ [x])) ⊔ (gFinal (sinceDual m1 m2) xs))).
Proof.
  generalize dependent x. induction xs using list_r_ind.
  + simpl. Reconstr.scrush.
  + intros. rewrite gNext_app. rewrite IHxs. unfold gFinal. rewrite IHxs.
    unfold mNextOut. unfold gFinal. repeat rewrite gNext_app.
    simpl. Reconstr.scrush.
Qed.

Lemma sinceDual_final {A : Type} (m1 m2 : Monitor A) (xs : list A) (x : A) :
  gFinal (sinceDual m1 m2) (xs ++ [x]) = (gFinal m2 (xs ++ [x]) ⊓ ((gFinal m1 (xs ++ [x])) ⊔ (gFinal (sinceDual m1 m2) xs))).
Proof.
  pose proof (@sinceDual_state A m1 m2 xs x). unfold gFinal. Reconstr.scrush.
Qed.

Lemma sinceDual_correctness {A : Type} (f1 f2 : Formula) (m1 m2 : Monitor A):
  implements m1 f1
  -> implements m2 f2
  -> implements (sinceDual m1 m2) (FSinceDual Val f1 f2).
Proof.
  unfold implements. intros.
  induction l using list_r_ind.
  - simpl. unfold gFinal. unfold finite_meet. simpl. unfold finite_join.
    simpl. rewrite join_bottom_r. rewrite meet_top_l. now rewrite <- H0.
  - rewrite sinceDual_inductive by exact distributiveLattice_val.
    rewrite sinceDual_final.
    rewrite IHl. rewrite H. rewrite H0.
    rewrite meet_comm. now rewrite join_comm.
Qed.

(* Bounded version of the always and sometime modalities *)

Definition mAlwaysWithin {A : Type} (hi : nat) (m : Monitor A) : Monitor A :=
  @mWinFold Val meetMonoid A m hi.

Lemma mAlwaysWithin_correctness {A : Type} (m : Monitor A) (hi : nat) (f : Formula):
  implements m f
  -> implements (mAlwaysWithin hi m) (FAlwaysWithin Val hi f).
Proof.
  unfold implements. intros.
  unfold mAlwaysWithin. rewrite mWinFold_final.
  simpl robustness. rewrite gCollect_prefixes_lastn.
  unfold finite_op. unfold finite_meet. f_equal. now apply map_ext.
Qed.

Definition mSometimeWithin {A : Type} (hi : nat) (m : Monitor A) : Monitor A :=
  @mWinFold Val joinMonoid A m hi.

Lemma mSometimeWithin_correctness {A : Type} (m : Monitor A) (hi : nat) (f : Formula):
  implements m f
  -> implements (mSometimeWithin hi m) (FSometimeWithin Val hi f).
Proof.
  unfold implements. intros.
  unfold mSometimeWithin. rewrite mWinFold_final.
  simpl robustness. rewrite gCollect_prefixes_lastn.
  unfold finite_op. unfold finite_join. f_equal. now apply map_ext.
Qed.


(** This is the compilation function **)

Fixpoint toMonitor {A : Type} (f : Formula) : Monitor A :=
  match f with
  | FAtomic _ g => monLift g
  | FDelay _ n g => mDelay n (toMonitor g)
  | FDelayDual _ n g => mDelayDual n (toMonitor g)
  | FAnd _ g h => mAnd (toMonitor g) (toMonitor h)
  | FOr _ g h => mOr (toMonitor g) (toMonitor h)
  | FSometime _ g => mSometime (toMonitor g)
  | FAlways _ g => mAlways (toMonitor g)
  | FSince _  g h => since (toMonitor g) (toMonitor h)
  | FSinceDual _ g h => sinceDual (toMonitor g) (toMonitor h)
  | FSometimeWithin _ hi g => mSometimeWithin hi (toMonitor g)
  | FAlwaysWithin _ hi g => mAlwaysWithin hi (toMonitor g)
  end.

Theorem toMonitor_correctness {A : Type} (f : Formula):
  implements (@toMonitor A f) f.
Proof.
  pose proof (@monLift_correctness A).
  pose proof (@mDelay_correctness A).
  pose proof (@mDelayDual_correctness A).
  pose proof (@sometime_correctness A).
  pose proof (@always_correctness A).
  pose proof (@since_correctness A).
  pose proof (@sinceDual_correctness A).
  pose proof (@mAnd_correctness A).
  pose proof (@mOr_correctness A).
  pose proof (@mSometimeWithin_correctness A).
  pose proof (@mAlwaysWithin_correctness A).
  induction f; Reconstr.scrush.
Qed.
