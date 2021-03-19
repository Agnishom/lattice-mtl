(** Properties of the function lastn. This is the last n elements of a finite list *)

Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.

Require Import Induction.
Require Import Last.

Section lastn.

  Definition lastn {A : Type} (n : nat) (xs : list A) := rev (firstn n (rev xs)).

  Definition skiplastn {A : Type} (n : nat) (xs : list A) := rev (skipn n (rev xs)).

  Lemma lastn_skiplastn {A : Type} (n : nat) (xs : list A) :
    skiplastn n xs ++ lastn n xs = xs.
  Proof.
    unfold skiplastn. unfold lastn.
    rewrite <- rev_app_distr. rewrite firstn_skipn.
    now rewrite rev_involutive.
  Qed.


  Lemma lastn_all {A : Type} (l : list A) :
    lastn (length l) l = l.
  Proof.
    unfold lastn. rewrite <- rev_length. rewrite firstn_all. rewrite rev_involutive.
    reflexivity.
  Qed.

  Lemma lastn_last {A : Type} (n : nat) (x : A) (xs : list A) :
    lastn (S n) (xs ++ [x]) = lastn n xs ++ [x].
  Proof.
    unfold lastn. rewrite rev_app_distr.
    auto.
  Qed.

  Lemma lastn_le_length {A : Type} (n : nat) (xs : list A) :
    length (lastn n xs) <= n.
  Proof.
    unfold lastn. rewrite rev_length. rewrite firstn_le_length.
    auto.
  Qed.

  Lemma lastn_0 {A : Type} (xs : list A) :
    lastn 0 xs = [].
  Proof.
    unfold lastn. auto.
  Qed.

  Lemma lastn_nil {A : Type} (n : nat) :
    (@lastn A) n [] = [].
  Proof.
    destruct n; auto.
  Qed.

  Lemma lastn_length {A : Type} (n : nat) (xs : list A) :
    length (lastn n xs) = min n (length xs).
  Proof.
    unfold lastn. rewrite rev_length. rewrite firstn_length.
    now rewrite rev_length.
  Qed.

  Lemma lastn_app {A : Type} (n : nat) (l1 l2 : list A) :
    lastn n (l1 ++ l2) = (lastn (n - length l2) l1) ++ (lastn n l2).
  Proof.
    unfold lastn at 1. rewrite rev_app_distr. rewrite firstn_app.
    rewrite rev_app_distr. rewrite rev_length; auto.
  Qed.

  Lemma lastn_app_2 {A : Type} (n : nat) (l1 l2 : list A) :
    lastn (length l2 + n) (l1 ++ l2) = (lastn n l1) ++ l2.
  Proof.
    unfold lastn at 1. rewrite rev_app_distr. rewrite <- rev_length.
    rewrite firstn_app_2. rewrite rev_app_distr.
    rewrite rev_involutive; auto.
  Qed.

  Lemma lastn_all2 {A : Type} (n : nat) (xs : list A) :
    n >= length xs
    -> lastn n xs = xs.
  Proof.
    unfold lastn. intros. rewrite firstn_all2. now rewrite rev_involutive.
    rewrite rev_length; lia.
  Qed.

  Lemma lastn_tail {A : Type} (n : nat) (xs : list A):
    n < length xs
    -> lastn n (tail xs) = lastn n xs.
  Proof.
    destruct xs.
    - auto.
    - simpl. unfold lastn.
      intros. simpl rev. rewrite firstn_app.
      rewrite rev_length. replace (n - length xs) with 0 by lia.
      rewrite rev_app_distr; auto.
  Qed.

Lemma tail_lastn {A : Type} (n : nat) (xs : list A):
  n < length xs
  -> tl (lastn (S n) xs) = lastn n xs.
Proof.
  unfold lastn. destruct (rev xs) eqn:E.
  - simpl. rewrite firstn_nil. auto.
  - simpl firstn. simpl.
    destruct n eqn:En.
    + auto.
    + simpl firstn at 2. simpl rev at 2.
      destruct (rev (firstn (S n0) l)) eqn:El.
      * simpl. intros.
        eapply f_equal in E. rewrite rev_length in E. simpl in E.
        eapply f_equal in El. rewrite rev_length in El.
        rewrite firstn_length in El. simpl length in El.
        lia.
      * simpl. intros. f_equal.
        eapply f_equal in El. rewrite rev_involutive in El.
        simpl rev in El.
        eapply f_equal in El. rewrite removelast_firstn in El.
        rewrite removelast_last in El.
        eapply f_equal in El; rewrite rev_involutive in El; auto.
        eapply f_equal in E.  rewrite rev_length in E.
        simpl in E. lia.
Qed.

Lemma last_firstn {A : Type} (n : nat) (xs ys : list A) (d : A):
  length xs > n
  -> last (firstn (S n) xs) d = last (firstn (S (length ys + n)) (ys ++ xs)) d.
Proof.
  intros.
  (* Step 1: last (firstn (S n) xs) = last (ys ++ (firstn (S n) xs)) *)
  remember (firstn (S n) xs) as blah.
  destruct blah using list_r_ind.
  { apply f_equal with (f := @length A) in Heqblah.
    rewrite firstn_length in Heqblah.
    replace (Init.Nat.min (S n) (length xs)) with (S n) in Heqblah by lia.
    inversion Heqblah.
  }
  (* Now we know that this expression is nonempty. *)
  clear IHblah.
  rewrite <- last_app_nonempty with (ys0 := ys).
  rewrite Heqblah. rewrite <- firstn_app_2.
  f_equal. replace ((length ys) + S n) with (S (length ys + n)) by lia. auto.
Qed.

Lemma last_firstn_lastn {A : Type} (m n : nat) (xs : list A) (d : A):
  length xs >= n ->
  n > m ->
  last (firstn (S m) (lastn n xs)) d = last (firstn (S (length xs - n + m)) xs) d.
Proof.
  intros.
  assert (length (lastn n xs) = n).
  { rewrite lastn_length. lia. }
  rewrite last_firstn with (ys := (skiplastn n xs)) by lia.
  rewrite lastn_skiplastn.
  f_equal; f_equal; f_equal; f_equal.
  rewrite <- lastn_skiplastn with (xs0 := xs) (n0 := n) at 2.
  rewrite app_length. lia.
Qed.

End lastn.
