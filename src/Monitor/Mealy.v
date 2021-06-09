(**

This file contains:

1. (Co-Inductive) Definition of a Mealy Machine
2. Notions of evaluation
3. Composition, Identity, First
4. Lifting Functions, Pointwise Operations, Unbounded Folds

*)

From NonEmptyList Require Import NonEmptyList.
From Algebra Require Import Monoid.
Require Import Coq.Lists.List.

Import NonEmptyNotations.
Import ListNotations.

Require Import Lia.
From Lemmas Require Import Lemmas.
Require Import Recdef.
Require Import FunInd.

CoInductive Mealy (A B : Type) : Type := {
  mOut : A -> B;
  mNext : A -> Mealy A B;
}.

Arguments mNext {A B}.
Arguments mOut {A B}.


(* Definition(s) of evaluation *)

Fixpoint gNext {A B : Type} (m : Mealy A B) (l : nonEmpty A) : Mealy A B :=
  match l with
  | singleton x => mNext m x
  | (xs :| x) => mNext (gNext m xs) x
  end.

Definition gOut {A B : Type} (m : Mealy A B) (l : nonEmpty A) : B :=
  match l with
  | singleton x => mOut m x
  | (xs :| x) => mOut (gNext m xs) x
  end.

Fixpoint gCollect {A B : Type} (m : Mealy A B) (l : nonEmpty A) : nonEmpty B :=
  match l with
  | singleton x => singleton (mOut m x)
  | (xs :| x) => (gCollect m xs) :| (gOut m l)
  end.

Lemma gCollect_gOut {A B : Type} (m : Mealy A B) (l : nonEmpty A) :
  gOut m l = latest (gCollect m l).
Proof.
  destruct l; auto.
Qed.

Lemma gCollect_neLength {A B : Type} (m : Mealy A B) (l : nonEmpty A):
  neLength (gCollect m l) = neLength l.
Proof.
  induction l; simpl; auto.
Qed.

(* Composition *)

CoFixpoint mCompose {A B C : Type} (m : Mealy A B) (n : Mealy B C) :=
  {| mOut x := mOut n (mOut m x) ;
     mNext x := mCompose (mNext m x) (mNext n (mOut m x))
  |}.

Notation "f >> g" := (mCompose f g) (at level 81, left associativity).

Lemma mCompose_state {A B C : Type} (m : Mealy A B) (n : Mealy B C) (l : nonEmpty A) :
  gNext (m >> n) l = ((gNext m l) >> (gNext n (gCollect m l))).
Proof.
  induction l; simpl; auto.
  - rewrite IHl. auto.
Qed.

Lemma mCompose_result {A B C : Type} (m : Mealy A B) (n : Mealy B C) (l : nonEmpty A) :
  gOut (m >> n) l = gOut n (gCollect m l).
Proof.
  destruct l; simpl; auto.
  - rewrite mCompose_state. auto.
Qed.

Lemma mCompose_results {A B C : Type} (m : Mealy A B) (n : Mealy B C) (l : nonEmpty A) :
  gCollect (m >> n) l = gCollect n (gCollect m l).
Proof.
  induction l.
  - auto.
  - simpl. rewrite mCompose_state.
    simpl. rewrite IHl. auto.
Qed.

Lemma mCompose_assoc {A B C D : Type} (m : Mealy A B) (n : Mealy B C) (o : Mealy C D) (l : nonEmpty A) :
  gOut ((m >> n) >> o) l = gOut (m >> (n >> o)) l.
Proof.
  induction l.
  - simpl. auto.
  - simpl. repeat rewrite mCompose_state.
    rewrite mCompose_results. auto.
Qed.

(* Lift *)

CoFixpoint mLift {A B : Type} (f : A -> B) : Mealy A B :=
  {| mOut x := f x;
     mNext _ := mLift f;
  |}.

Lemma mLift_state {A B : Type} (f : A -> B) (l : nonEmpty A) :
  gNext (mLift f) l = mLift f.
Proof.
  induction l; simpl; auto.
  - now rewrite IHl.
Qed.

Lemma mLift_result {A B : Type} (f : A -> B) (l : nonEmpty A) :
  gOut (mLift f) l = f (latest l).
Proof.
  destruct l; simpl; auto.
  - rewrite mLift_state. auto.
Qed.

Lemma mLift_results {A B : Type} (f : A -> B) (l : nonEmpty A) :
  gCollect (mLift f) l = neMap f l.
Proof.
  induction l; auto.
  - simpl. rewrite mLift_state.
    now rewrite IHl.
Qed.


(* Identity *)

Definition mIdentity {A : Type} : Mealy A A := mLift id.

Lemma mIdentity_state {A : Type} (l : nonEmpty A) :
  gNext mIdentity l = mIdentity.
Proof.
  unfold mIdentity; auto using mLift_state.
Qed.

Lemma mIdentity_result {A : Type} (l : nonEmpty A) :
  gOut mIdentity l = latest l.
Proof.
  unfold mIdentity; rewrite mLift_result; auto.
Qed.

Lemma mIdentity_results {A : Type} (l : nonEmpty A) :
  gCollect mIdentity l = l.
Proof.
  induction l; simpl; auto.
  - rewrite IHl. rewrite mIdentity_state. auto.
Qed.


Lemma mIdentity_mCompose_results {A B : Type} (m : Mealy A B) (l : nonEmpty A) :
  gCollect (mIdentity >> m) l = gCollect m l.
Proof.
  rewrite mCompose_results.
  rewrite mIdentity_results.
  auto.
Qed.

Lemma mCompose_mIdentity_results {A B : Type} (m : Mealy A B) (l : nonEmpty A) :
  gCollect (mIdentity >> m) l = gCollect m l.
Proof.
  rewrite mCompose_results.
  rewrite mIdentity_results.
  auto.
Qed.

Lemma mLift_mCompose_results {A B C : Type} (f : A -> B) (g : B -> C) (l : nonEmpty A) :
  gCollect (mLift (Basics.compose g f)) l = gCollect ((mLift f) >> (mLift g)) l.
Proof.
  induction l; auto.
  - simpl. rewrite mCompose_state.
    repeat rewrite mLift_state. simpl.
    rewrite IHl. auto.
Qed.
Lemma mLift_mCompose_result {A B C : Type} (f : A -> B) (g : B -> C) (l : nonEmpty A) :
  gOut (mLift (Basics.compose g f)) l = gOut ((mLift f) >> (mLift g)) l.
Proof.
  repeat rewrite gCollect_gOut.
  now rewrite mLift_mCompose_results.
Qed.

(* First *)

CoFixpoint mFirst {A B C: Type} (m : Mealy A B) : Mealy (A * C) (B * C) :=
  {| mOut xy  := match xy with (x , y) => (mOut m x, y) end ;
     mNext xy := match xy with (x, _ ) => mFirst (mNext m x) end ;
  |}.

Lemma mFirst_state {A B C : Type} (m : Mealy A B) (l : nonEmpty (A * C)) :
  gNext (mFirst m) l = mFirst (gNext m (unzip_fst l)).
Proof.
  induction l; destruct a; auto.
  - simpl. rewrite IHl. auto.
Qed.

Lemma mFirst_result {A B C : Type} (m : Mealy A B) (l : nonEmpty (A * C)) :
  gOut (mFirst m) l = ((gOut m (unzip_fst l)), snd (latest l)).
Proof.
  destruct l.
  - destruct p. auto.
  - destruct p. simpl. rewrite mFirst_state.
    auto.
Qed.

Definition fnFirst {A B C : Type} (f : A -> B) (xy : A * C) :=
  match xy with (x, y) => (f x, y) end.

Lemma mFirst_results {A B C : Type} (m : Mealy A B) (l : nonEmpty (A * C)) :
  gCollect (mFirst m) l = neZip (gCollect m (unzip_fst l)) (unzip_snd l).
Proof.
  induction l; destruct a.
  - auto.
  - simpl. rewrite IHl.
    rewrite mFirst_state. auto.
Qed.

Lemma mLift_mFirst {A B C : Type} (f : A -> B) (l : nonEmpty (A * C)):
  gOut (mFirst (mLift f)) l = gOut (mLift (fnFirst f)) l.
Proof.
  destruct l.
  - auto.
  - simpl. repeat rewrite mFirst_state.
    repeat rewrite mLift_state.
    auto.
Qed.

Lemma mFirst_mCompose {A B C D : Type} (m : Mealy A B) (n : Mealy B C) (l : nonEmpty (A * D)) :
  gOut (mFirst (m >> n)) l = gOut ((mFirst m) >> (mFirst n)) l.
Proof.
  destruct l as [ [a b] | l [a b]]; simpl; auto.
  - rewrite mCompose_state.
    rewrite mFirst_state.
    rewrite mCompose_state.
    rewrite mFirst_state.
    simpl. rewrite mFirst_results.
    rewrite mFirst_state.
    simpl. rewrite unzip_fst_neZip.
    auto.
    + rewrite gCollect_neLength.
      unfold unzip_fst. unfold unzip_snd.
      repeat rewrite neMap_neLength.
      auto.
Qed.

(* Parallel *)
CoFixpoint mPar {A B C: Type} (m : Mealy A B) (n : Mealy A C) : Mealy A (B * C) :=
  {| mOut x  := (mOut m x, mOut n x);
     mNext x := mPar (mNext m x) (mNext n x);
  |}.

Lemma mPar_state {A B C : Type} (m : Mealy A B) (n : Mealy A C) (l : nonEmpty A):
  gNext (mPar m n) l = mPar (gNext m l) (gNext n l).
Proof.
  induction l; simpl; auto.
  - rewrite IHl. auto.
Qed.

Lemma mPar_result {A B C : Type} (m : Mealy A B) (n : Mealy A C) (l : nonEmpty A) :
  gOut (mPar m n) l = (gOut m l, gOut n l).
Proof.
  destruct l.
  - auto.
  - simpl. rewrite mPar_state. auto.
Qed.

Lemma mPar_results {A B C : Type} (m : Mealy A B) (n : Mealy A C) (l : nonEmpty A) :
  gCollect (mPar m n) l = neZip (gCollect m l) (gCollect n l).
Proof.
  induction l; simpl; auto.
  - rewrite IHl. f_equal.
    rewrite mPar_state. auto.
Qed.

Lemma mPar_mCompose {A B C D : Type} (m : Mealy A B) (n : Mealy A C) (o : Mealy (B * C) D) (l : nonEmpty A) :
  gOut ((mPar m n) >> o) l = gOut o (neZip (gCollect m l) (gCollect n l)).
Proof.
  rewrite mCompose_result. now rewrite mPar_results.
Qed.


(* Binary Operations *)

CoFixpoint mBinOp {A B C D : Type} (op : B -> C -> D) (m : Mealy A B) (n : Mealy A C) : Mealy A D :=
  {|
  mOut (a : A) := op (mOut m a) (mOut n a);
  mNext (a : A) := mBinOp op (mNext m a) (mNext n a);
  |}.

Lemma mBinOp_state {A B C D} : forall (op : B -> C -> D) (m : Mealy A B) n l, gNext (mBinOp op m n) l = mBinOp op (gNext m l) (gNext n l).
Proof.
  induction l; simpl; auto.
  - rewrite IHl. auto.
Qed.

Lemma mBinOp_result {A B C D} : forall (op : B -> C -> D) (m : Mealy A B) n l, gOut (mBinOp op m n) l = op (gOut m l) (gOut n l).
Proof.
  destruct l; simpl; auto.
  - rewrite mBinOp_state. auto.
Qed.

(* Unbounded Folds *)

CoFixpoint mFold {A B : Type} (op : B -> B -> B) (m : Mealy A B) (init : B) : Mealy A B :=
  {|
  mOut (a : A) := op init (mOut m a);
  mNext (a : A) := mFold op (mNext m a) (op init (mOut m a));
  |}.

Lemma mFold_state {A B} (op : B -> B -> B) (m : Mealy A B) :
    forall init l, gNext (mFold op m init) l = mFold op (gNext m l) (fold_left op (rev (toList (gCollect m l))) init).
Proof.
  induction l.
  - auto.
  - simpl. rewrite IHl. rewrite fold_left_app. auto.
Qed.

Lemma mFold_result {A B} (op : B -> B -> B) (m : Mealy A B) :
  forall init l, gOut (mFold op m init) l = fold_left op (rev (toList (gCollect m l))) init.
Proof.
  destruct l; auto.
  - simpl. rewrite mFold_state. rewrite fold_left_app. auto.
Qed.
