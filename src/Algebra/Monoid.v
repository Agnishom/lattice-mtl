Require Import Coq.Lists.List.
Require Import Lia.
Require Import ssreflect.

From Lemmas Require Import Lemmas.

Import ListNotations.

Class Monoid (A : Type) := {
  op : A -> A -> A;
  unit : A;

  op_unit_r : forall x, op x unit = x;
  op_unit_l : forall x, op unit x = x;
  op_assoc : forall x y z, op x (op y z) = op (op x y) z;
}.

Section monoid_Sum.

  Variable (Val : Type).
  Context {monoid_val : Monoid Val}.

  Generalizable All Variables.


  (** finite_op [x1, x2, ... xn] = x1 `op` x2 `op` ... `op` xn **)
  Definition finite_op (xs : list Val) :=
    fold_left op xs unit.

  Lemma finite_op_singleton :
    forall x, finite_op [x] = x.
  Proof.
    unfold finite_op. simpl. intros. now rewrite op_unit_l.
  Qed.

  Lemma finite_op_app :
    forall xs ys, op (finite_op xs) (finite_op ys) = finite_op (xs ++ ys).
  Proof.
    unfold finite_op. intros. rewrite fold_left_app.
    induction ys using list_r_ind.
    - simpl. now rewrite op_unit_r.
    - repeat rewrite fold_left_app. simpl.
      rewrite op_assoc. now rewrite IHys.
  Qed.

  (** (f start) `op` (f (start + 1)) `op` ... `op` (f (start + length - 1)) **)
  Definition op_i (start : nat) (length : nat) (f : nat -> Val) :=
    finite_op (map f (seq start length)).

  (** (f lo) `op` (f (lo + 1)) ... `op` (f hi) **)
  Definition op_b (lo : nat) (hi : nat) :=
    op_i lo (S hi - lo).

  Lemma op_i_ext (start : nat) (length : nat) (f g : nat -> Val)
    : (forall a, f a = g a) -> op_i start length f = op_i start length g.
  Proof.
    intros. unfold op_i. under map_ext do rewrite H. reflexivity.
  Qed.
  Lemma op_i_ext_in (start : nat) (length : nat) (f g : nat -> Val)
    : (forall a, start <= a -> a <= start + length -> f a = g a)
      -> op_i start length f = op_i start length g.
  Proof.
    intros. unfold op_i. f_equal.
    apply map_ext_in. intros. rewrite -> in_seq in H0. rewrite H.
    lia. lia. reflexivity.
  Qed.
  Lemma op_b_ext (lo hi : nat) (f g : nat -> Val)
    : (forall a, f a = g a) -> op_b lo hi f = op_b lo hi g.
  Proof.
    intros. unfold op_b. under op_i_ext do rewrite H. reflexivity.
  Qed.
  Lemma op_b_ext_in (lo hi : nat) (f g : nat -> Val)
    : (forall a, lo <= a -> a <= hi -> f a = g a)
      -> op_b lo hi f = op_b lo hi g.
  Proof.
    intros. unfold op_b. unfold op_i. f_equal.
    apply map_ext_in. intros. rewrite -> in_seq in H0. rewrite H.
    lia. lia. reflexivity.
  Qed.


  Lemma op_i_unit :
    forall s l, op_i s l (fun _ => unit) = unit.
  Proof.
    intros. generalize dependent s. unfold op_i. unfold finite_op. induction l.
    - auto.
    - intros. simpl. rewrite op_unit_r. now rewrite IHl.
  Qed.

  Lemma op_i_unit_ext :
    forall s l f,
      (forall i, f i = unit)
      -> op_i s l f = unit.
  Proof.
    intros. generalize dependent s. unfold op_i. unfold finite_op. induction l.
    - auto.
    - intros. simpl. rewrite H. rewrite op_unit_r. now rewrite IHl.
  Qed.

  Lemma op_b_unit :
    forall lo hi, op_b lo hi (fun _ => unit) = unit.
  Proof.
    unfold op_b. pose proof op_i_unit. auto.
  Qed.

  Lemma op_b_unit_ext :
    forall s l f,
      (forall i, f i = unit)
      -> op_b s l f = unit.
  Proof.
    unfold op_b. pose proof op_i_unit_ext. auto.
  Qed.


  Lemma op_i_unit_ext_in :
    forall s l f,
      (forall i, s <= i -> i <= s + l -> f i = unit)
      -> op_i s l f = unit.
  Proof.
    intros. rewrite ->op_i_ext_in with (g := (fun _ => unit)) by auto.
    auto using op_i_unit.
  Qed.

  Lemma op_b_unit_ext_in :
    forall lo hi f,
      (forall i, lo <= i -> i <= hi -> f i = unit)
      -> op_b lo hi f = unit.
  Proof.
    intros. rewrite ->op_b_ext_in with (g := (fun _ => unit)) by auto.
    auto using op_b_unit.
  Qed.

  Lemma op_i_shift :
    forall f h l s, op_i s l (fun i => f (i + h)) = op_i (s + h) l f.
  Proof.
    unfold op_i. unfold finite_op. induction l.
    - auto.
    - intros. replace (S l) with (l + 1) by lia.
      repeat rewrite seq_app. repeat rewrite map_app.
      repeat rewrite fold_left_app. rewrite IHl.
      simpl. f_equal. f_equal. lia.
  Qed.

  Lemma op_i_shift_ext :
    forall f g h l s,
      (forall i, g i = f (i + h))
      -> op_i s l g = op_i (s + h) l f.
  Proof.
    intros. rewrite ->op_i_ext with (g := (fun i => f (i + h))) by auto.
    auto using op_i_shift.
  Qed.

  Lemma op_i_shift_ext_in :
    forall f g h l s,
      (forall i, s <= i -> i <= s + l -> g i = f (i + h))
      -> op_i s l g = op_i (s + h) l f.
  Proof.
    intros. rewrite ->op_i_ext_in with (g := (fun i => f (i + h))) by auto.
    auto using op_i_shift.
  Qed.

  Lemma op_b_shift :
    forall f h lo hi, op_b lo hi (fun i => f (i + h)) = op_b (lo + h) (hi + h) f.
  Proof.
    unfold op_b. intros.
    replace (S (hi + h) - (lo + h)) with (S hi - lo) by lia.
    auto using op_i_shift.
  Qed.

  Lemma op_b_shift_ext :
    forall f g h lo hi,
      (forall i, g i = f (i + h))
      -> op_b lo hi g = op_b (lo + h) (hi + h) f.
  Proof.
    intros. rewrite -> op_b_ext with (g := (fun i => f (i + h))) by auto.
    apply op_b_shift.
  Qed.

  Lemma op_b_shift_ext_in :
    forall f g h lo hi,
      (forall i, lo <= i -> i <= hi -> g i = f (i + h))
      -> op_b lo hi g = op_b (lo + h) (hi + h) f.
  Proof.
    intros. rewrite -> op_b_ext_in with (g := (fun i => f (i + h))) by auto.
    apply op_b_shift.
  Qed.


  Lemma op_i_app :
    forall f l1 l2 s, op_i s (l1 + l2) f = op (op_i s l1 f) (op_i (s + l1) l2 f).
  Proof.
    unfold op_i. intros. rewrite seq_app. rewrite map_app. now rewrite finite_op_app.
  Qed.

  Lemma op_b_app :
    forall f lo hi1 hi2,
      lo <= hi1 -> hi1 < hi2 ->
      op_b lo hi2 f = op (op_b lo hi1 f) (op_b (S hi1) hi2 f).
  Proof.
    intros. unfold op_b.
    remember lo as s. remember (S hi1 - s) as l1.
    assert (S hi1 = lo + l1) by lia.
    remember (S hi2 - S hi1) as l2.
    assert (S hi2 - s = l1 + l2) by lia.
    rewrite ->Heqs at 1 3. rewrite H2. rewrite H1.
    apply op_i_app.
  Qed.



  Lemma finite_op_fold_left :
    forall x l, op x (finite_op l) = fold_left op l x.
  Proof.
    intros. replace x with (finite_op [x]) by now rewrite finite_op_singleton.
    rewrite finite_op_app. simpl. unfold finite_op. reflexivity.
  Qed.

  Lemma finite_op_repeat_unit :
    forall n, finite_op (repeat unit n) = unit.
  Proof.
    induction n.
    - auto.
    - simpl. replace (unit :: repeat unit n) with ([unit] ++ repeat unit n) by auto.
      rewrite <- finite_op_app. rewrite finite_op_singleton. rewrite op_unit_l.
      apply IHn.
  Qed.


End monoid_Sum.
