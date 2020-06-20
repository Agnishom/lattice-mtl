Require Import Coq.Lists.List.
Require Import Lia.

Require Import MTLTactics.

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

  Definition op_i (start : nat) (length : nat) (f : nat -> Val) :=
    finite_op (map f (seq start length)).

  Lemma op_i_unit :
    forall s l, op_i s l (fun _ => unit) = unit.
  Proof.
    intros. generalize dependent s. unfold op_i. unfold finite_op. induction l.
    - auto.
    - intros. simpl. rewrite op_unit_r. now rewrite IHl.
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

  Lemma op_i_app :
    forall f l1 l2 s, op_i s (l1 + l2) f = op (op_i s l1 f) (op_i (s + l1) l2 f).
  Proof.
    unfold op_i. intros. rewrite seq_app. rewrite map_app. now rewrite finite_op_app.
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
