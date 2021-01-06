Require Import Coq.Lists.List.
Require Import Lia.

Require Import Lastn.

Import ListNotations.

Section Repeat.

  Lemma repeat_snoc_cons {A : Type} (x : A) (n : nat) :
    repeat x n ++ [x] = x :: repeat x n.
  Proof.
    induction n; auto.
    - simpl. now rewrite IHn.
  Qed.

  Fixpoint repeatAux {A : Type} (x : A) (n : nat) (acc : list A) :=
    match n with
    | O => acc
    | S k => repeatAux x k (x :: acc)
  end.

  Definition repeat' {A : Type} (x : A) (n : nat) :=
    repeatAux x n [].

  Lemma repeatAux_correctness {A : Type} (x : A) (xs : list A) (n : nat) :
    repeatAux x n xs = (repeat x n) ++ xs.
  Proof.
    generalize dependent xs. induction n; [auto | ].
    intros. simpl repeat. simpl repeatAux. rewrite IHn.
    rewrite <- repeat_snoc_cons.
    now rewrite <- app_assoc.
  Qed.

  Lemma repeat_repeat' {A : Type} (x : A) (n : nat) :
    repeat' x n = (repeat x n).
  Proof.
    unfold repeat'. rewrite repeatAux_correctness.
	  now simpl_list.
  Qed.

  Lemma repeat_rev {A}: forall (a : A) n, repeat a n = rev (repeat a n).
  Proof.
    induction n; auto.
    - simpl. rewrite <- IHn.
      auto using repeat_snoc_cons.
  Qed.

  Lemma repeat_app {A} (a : A) :
    forall i j, repeat a i ++ repeat a j = repeat a (i + j).
  Proof.
    intros. revert i. induction j.
    - simpl. intros. replace (i + 0) with i by lia. now simpl_list.
    - simpl. rewrite <- repeat_snoc_cons.
      intros. rewrite app_assoc. rewrite IHj.
      rewrite repeat_snoc_cons.
      replace (i + S j) with (S (i + j)) by lia.
      auto.
  Qed.

  Lemma repeat_cancellative {A} (a : A) :
    forall i j, repeat a i = repeat a j -> i = j.
  Proof.
    intros.
    eapply f_equal in H.
    repeat rewrite repeat_length in H. apply H.
  Qed.

  Lemma repeat_inv_app {A} (a : A) :
    forall i j xs, repeat a i ++ xs = repeat a j
              -> xs = repeat a (j - i).
  Proof.
    intros.
    assert (H' := H).
    eapply f_equal in H. rewrite app_length in H.
    repeat rewrite repeat_length in H.
    subst j. replace (i + length xs - i) with (length xs) by lia.
    rewrite <- repeat_app in H'. now apply app_inv_head in H'.
  Qed.


  Lemma firstn_repeat {A : Type} :
    forall (a : A) i j, firstn i (repeat a j) = repeat a (min i j).
  Proof.
    intros. revert i. induction j; intros.
    - replace (min i 0) with 0 by lia.
      rewrite firstn_nil. auto.
    - simpl. destruct i.
      + auto.
      + simpl. rewrite IHj. auto.
  Qed.

  Lemma skipn_repeat {A : Type} :
    forall (a : A) i j, skipn i (repeat a j) = repeat a (j - i).
  Proof.
    intros.
    destruct (Compare_dec.le_lt_dec i j).
    + pose proof (firstn_skipn i (repeat a j)).
      rewrite firstn_repeat in H.
      apply repeat_inv_app.
      replace (min i j) with i in H by lia. auto.
    + replace (j - i) with 0 by lia.
      simpl. rewrite skipn_all2. auto.
      rewrite repeat_length. lia.
  Qed.

  Lemma lastn_repeat {A : Type} :
    forall (a : A) i j, lastn i (repeat a j) = repeat a (min i j).
  Proof.
    intros.
    unfold lastn. rewrite <- repeat_rev.
    rewrite firstn_repeat. now rewrite <- repeat_rev.
  Qed.


  Lemma in_repeat {A} (a x : A) (n : nat) :
    In x (repeat a n) -> a = x.
  Proof.
    induction n; simpl; intuition.
  Qed.

  Lemma nth_repeat {A : Type} (a d : A) (n i : nat):
    i < n
    -> nth i (repeat a n) d = a.
  Proof.
    intros.
    assert (i < length (repeat a n)) by now rewrite repeat_length.
    eapply nth_In in H0.
    eapply in_repeat in H0.
    symmetry in H0. apply H0.
  Qed.

  Lemma nth_repeat2 {A : Type} (a : A) (n i : nat):
    nth i (repeat a n) a = a.
  Proof.
    intros. destruct (Compare_dec.le_lt_dec n i).
    - apply nth_overflow. now rewrite repeat_length.
    - now apply nth_repeat.
  Qed.

End Repeat.
