(**

This file contains:

1. The type for nonEmpty lists.
  - with some notation for these lists.
2. Conversions to and from nonEmpty lists.
3. Some useful functions on these lists.

 *)

Require Import Coq.Lists.List.

Require Import Lia.

Inductive nonEmpty (A : Type) : Type :=
| singleton : A -> nonEmpty A
| snocNE : nonEmpty A -> A -> nonEmpty A.

Arguments singleton {A}.
Arguments snocNE {A}.

Declare Scope nonempty_scope.
Delimit Scope nonempty_scope with nonEmpty.
Bind Scope nonempty_scope with nonEmpty.

Open Scope nonempty_scope.


Module NonEmptyNotations.

  Notation "< x >" := (singleton x) : nonempty_scope.
  Infix ":|" := snocNE (at level 61, left associativity) : nonempty_scope.
  Notation "< a ; b ; .. ; c ; d >" :=
   (snocNE (snocNE .. (snocNE (singleton a) b) .. c) d) : nonempty_scope.

End NonEmptyNotations.

Import NonEmptyNotations.

Section NonEmpty.

  Variable A : Type.

  Fixpoint toList (l : nonEmpty A) :=
    match l with
    | singleton x => (cons x nil)
    | snocNE xs x => (cons x (toList xs))
    end.

  Definition latest (l : nonEmpty A) :=
    match l with
    | singleton x => x
    | xs :| x => x
    end.

  Definition list_nil_dec (l : list A) :
    {l = nil} + {l <> nil}.
  Proof.
    destruct l.
    - left. reflexivity.
    - right. discriminate.
  Defined.

  Fixpoint fromList (l : list A) : (l <> nil) -> nonEmpty A :=
    (match l with
            | nil => fun (H : nil <> nil) => ltac:(intuition)
            | (cons x xs) =>
              fun (_ : (cons x xs) <> nil) =>
              match (list_nil_dec xs) with
              | left _ => singleton x
              | right pr => snocNE (fromList xs pr) x
              end
     end).

  Lemma fromList_toList (l : list A) (H : l <> nil) :
    toList (fromList l H) = l.
  Proof.
    destruct l; [congruence | ].
    revert H. revert a.  induction l.
    - intros. simpl. destruct (list_nil_dec nil).
      + reflexivity.
      + congruence.
    - intros. remember (cons a l) as al. simpl.
      destruct (list_nil_dec al); [congruence | ].
      simpl. f_equal.
      subst al. rewrite IHl. reflexivity.
  Qed.

  Lemma toList_nonEmpty (l : nonEmpty A) :
    toList l <> nil.
  Proof.
    destruct l; simpl; congruence.
  Defined.

  Lemma toList_fromList_forall (l : nonEmpty A) :
    forall H, fromList (toList l) H = l.
  Proof.
    induction l.
    - simpl.
      destruct (list_nil_dec nil); [reflexivity | congruence].
    - intros. simpl.
      destruct (list_nil_dec (toList l)).
      + now apply toList_nonEmpty in e.
      + f_equal. apply IHl.
  Qed.

  Lemma toList_fromList (l : nonEmpty A) :
    exists H, fromList (toList l) H = l.
  Proof.
    exists (toList_nonEmpty l). auto using toList_fromList_forall.
  Qed.

End NonEmpty.

Arguments latest {A}.
Arguments toList {A}.
Arguments fromList {A}.
Arguments toList_nonEmpty {A}.

Section Transport.

  Variable A B : Type.

  Definition preserves_ne (f : list A -> list B) :=
    forall l, l <> nil -> f l <> nil.

  Definition neLift (f : list A -> list B) (H : preserves_ne f) (l : nonEmpty A) :=
    fromList (f (toList l)) (H (toList l) (toList_nonEmpty l)).

  Definition listLift (f : nonEmpty A -> nonEmpty A) (l : list A) (H : l <> nil) :=
    toList (f (fromList l H)).

End Transport.

Section NonEmptyFunctions.

  Fixpoint neMap {A B} (f : A -> B) (l : nonEmpty A) : nonEmpty B :=
    match l with
    | (singleton x) => singleton (f x)
    | (xs :| x) => (neMap f xs) :| f x
    end.

  Fixpoint neNth {A} (d : A) (n : nat) (l : nonEmpty A) :=
    match l, n with
    | (singleton x), 0 => x
    | (xs :| x), 0 => x
    | (singleton x), S n' => d
    | (xs :| x), S n' => neNth d n' xs
    end.


  Fixpoint neLength {A} (l : nonEmpty A) : nat :=
    match l with
    | (singleton x) => 1
    | (xs :| x) => S (neLength xs)
    end.

  Lemma length_toList {A} (l : nonEmpty A) :
    length (toList l) = neLength l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma length_toList1 {A} (l : nonEmpty A) :
    length (toList l) >= 1.
  Proof.
    rewrite length_toList.
    induction l; simpl; auto.
  Qed.

  Lemma nth_latest {A} (l : nonEmpty A) :
    forall d, nth 0 (toList l) d = latest l.
  Proof.
    destruct l; auto.
  Qed.

  Lemma neMap_neLength {A B} (f : A -> B) (l : nonEmpty A) :
    neLength (neMap f l) = neLength l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Definition unzip_fst {A B : Type} (l : nonEmpty (A * B)) : nonEmpty A :=
    neMap fst l.

  Definition unzip_snd {A B : Type} (l : nonEmpty (A * B)) : nonEmpty B :=
    neMap snd l.

  Fixpoint neZip {A B : Type} (l1 : nonEmpty A) (l2 : nonEmpty B) : nonEmpty (A * B) :=
    match l1, l2 with
    | (singleton x), (singleton y) => singleton (x, y)
    | (xs :| x), (ys :| y) => (neZip xs ys) :| (x, y)
    | (singleton x), (ys :| y) => singleton (x, y)
    | (xs :| x), (singleton y) => singleton (x, y)
    end.

  Lemma unzip_fst_neZip {A B : Type} (l1 : nonEmpty A) (l2 : nonEmpty B) :
    neLength l1 = neLength l2 -> unzip_fst (neZip l1 l2) = l1.
  Proof.
    revert l2. induction l1.
    - simpl. intros.
      destruct l2.
      + auto.
      + auto.
    - simpl. intros.
      destruct l2.
      + destruct l1; simpl in H; lia.
      + simpl in H. inversion H. apply IHl1 in H1.
        unfold unzip_fst in *. simpl.
        f_equal. auto.
  Qed.

  Fixpoint neLastn {A : Type} (l : nonEmpty A) (n : nat) :=
    match n with
    | 0 => nil
    | S n' => match l with
               | (singleton x) => (cons x nil)
               | (xs :| x) => (cons x (neLastn xs n'))
             end
    end.

End NonEmptyFunctions.
