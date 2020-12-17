Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.

Section Induction.

  (* List induction by length *)
  Lemma list_length_ind {A : Type}: forall (P : list A -> Prop),
    (forall xs, (forall (l : list A), length l < length xs -> P l) -> P xs)
    -> forall xs, P xs.
  Proof.
    intros P H.
    assert (forall (xs : list A) (l : list A), length l <= length xs -> P l) as H_ind.
    {
      induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.

  (* A theorem for inducting on lists from left to right *)
  Lemma list_r_ind {A : Type}: forall (P : list A -> Prop),
                 P []
                 -> (forall x (xs : list A), (P xs -> P (xs ++ [x])))
                 -> forall xs, P xs.
  Proof.
    induction xs using list_length_ind.
    destruct xs.
    - auto.
    - rewrite app_removelast_last with (l := (a :: xs)) (d := a) by discriminate.
      apply H0. apply H1.
      rewrite app_removelast_last with (l := (a :: xs)) (d := a) at 2 by discriminate.
      rewrite app_length. simpl length at 3. lia.
  Qed.


End Induction.

Section last.

Lemma last_nonempty {A : Type} : forall (x d : A) l,
    last (l ++ [x]) d = x.
Proof.
  induction l.
  - auto.
  - replace ((a :: l) ++ [x]) with (a :: (l ++ [x])) by auto.
    remember (l ++ [x]). destruct l0.
    + destruct l; inversion Heql0.
    + replace (last (a :: a0 :: l0)) with (last (a0 :: l0)) by auto.
      auto.
Qed.

Lemma last_app_nonempty {A : Type} : forall (x d : A) xs ys,
    last (ys ++ (xs ++ [x])) d = last (xs ++ [x]) d.
Proof.
  intros. rewrite app_assoc. rewrite last_nonempty. rewrite last_nonempty.
  auto.
Qed.

Lemma last_inversion {A : Type} : forall (x y : A) xs ys,
    xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
  intros. apply (f_equal (@rev A)) in H.
  repeat rewrite (rev_app_distr) in H.
  simpl in H. inversion H. apply (f_equal (@rev A)) in H2.
  repeat rewrite rev_involutive in H2.
  auto.
Qed.

Lemma removelast_nonempty {A : Type} : forall (x : A) xs,
    removelast (xs ++ [x]) = xs.
Proof.
  induction xs.
  - auto.
  - replace ((a :: xs) ++ [x]) with (a :: (xs ++ [x])) by reflexivity.
    simpl. rewrite IHxs. destruct (xs ++ [x]) eqn:E.
    + destruct xs; inversion E.
    + reflexivity.
Qed.

End last.


Section nth.

  Lemma nth_hd_error {A : Type} : forall (l : list A) (d : A) (n : nat),
    n < length l ->
    hd_error (rev (firstn (S n) l)) = Some (nth n l d).
  Proof.
    induction l using list_r_ind.
    - simpl. lia.
    - intros. rewrite app_length in H.
      simpl in H. replace (length l + 1) with (S (length l)) in H by lia.
      rewrite PeanoNat.Nat.lt_succ_r in H.
      rewrite firstn_app. rewrite rev_app_distr.
      destruct (Compare_dec.le_lt_eq_dec _ _ H).
      + replace (S n - length l) with 0 by lia.
        simpl firstn at 1. simpl rev at 1. rewrite app_nil_l.
        rewrite IHl with (d := d).
        now rewrite app_nth1 by auto. auto.
      + replace (S n - length l) with 1 by lia. simpl firstn at 1.
        simpl rev at 1. simpl hd_error.
        rewrite app_nth2. replace (n - length l) with 0 by lia.
        auto. lia.
  Qed.


End nth.


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
