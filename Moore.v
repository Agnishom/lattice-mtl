From Hammer Require Import Hammer.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import FunInd.
Require Import Recdef.

Require Import MTLTactics.
Require Import Monoid.
Require Import Coq.Arith.PeanoNat.


Import ListNotations.

(* Definition of Moore Machine *)
CoInductive Moore (A B: Type) : Type := {
 mOut: B;
 mNext: A -> Moore A B;
}.

Arguments mNext {A B}.
Arguments mOut {A B}.


Definition mNextOut {A B : Type} (m : Moore A B) (a : A) : B :=
  mOut (mNext m a).


(* Definition(s) of evaluation *)

Definition gNext {A B : Type} (m : Moore A B) (l : list A) : Moore A B :=
  fold_left mNext l m.

Definition gFinal {A B : Type} (m : Moore A B) (l : list A) : B :=
  mOut (gNext m l).

(* A notion of a machine that gathers inputs *)

CoFixpoint collectMooreAux {A B : Type} (m : Moore A B) (soFar : list B) : Moore A (list B) := {|
   mOut  := soFar;
   mNext (a : A) := collectMooreAux (mNext m a) (soFar ++ [mNextOut m a]);
|}.

Definition collectMoore {A B : Type} (m : Moore A B) : Moore A (list B) :=
  collectMooreAux m [mOut m].

Definition gCollectNext {A B : Type} (m : Moore A B) (l : list A): Moore A (list B) :=
  gNext (collectMoore m) l.

Definition gCollect {A B : Type} (m : Moore A B) (l : list A) : list B :=
  mOut (gCollectNext m l).

(* Some simple lemmas about the nature of evaluation *)

Lemma gNext_app {A B : Type} (m : Moore A B) (l1 l2 : list A) :
  gNext m (l1 ++ l2) = gNext (gNext m l1) l2.
Proof.
  pose proof fold_left_app. Reconstr.scrush.
Qed.

Lemma gFinal_app {A B : Type} (m : Moore A B) (l1 l2 : list A) :
  gFinal m (l1 ++ l2) = gFinal (gNext m l1) l2.
Proof.
  pose proof (gNext_app m). Reconstr.reasy Reconstr.Empty (@mOut, @gFinal).
Qed.

Lemma gCollectNext_last {A B : Type} (m : Moore A B) (xs: list A) (x : A):
  gCollectNext m (xs ++ [x]) = collectMooreAux (gNext m (xs ++ [x]))
                                               ((gCollect m xs) ++ [gFinal m (xs ++ [x])]).
Proof.
  unfold gCollectNext. unfold gFinal. unfold collectMoore.
  rewrite gNext_app. rewrite gNext_app.
  generalize dependent x.
  induction xs using list_r_ind.
  - auto.
  - rewrite gNext_app. rewrite IHxs.
    simpl. rewrite gNext_app. unfold gCollect. unfold gFinal. unfold gCollectNext. rewrite gNext_app.
    unfold collectMoore. rewrite IHxs. simpl. auto.
Qed.

Lemma gCollect_last {A B : Type} (m : Moore A B) (xs : list A) (x : A):
  gCollect m (xs ++ [x]) = ((gCollect m xs) ++ [gFinal m (xs ++ [x])]).
Proof.
  pose proof (@gCollectNext_last A B).
  unfold gCollect at 1. Reconstr.scrush.
Qed.


Lemma gCollectNext_app {A B : Type} (m : Moore A B) (xs ys : list A) (y : A) :
  gCollectNext m ((xs ++ [y]) ++ ys) = collectMooreAux (gNext m ((xs ++ [y]) ++ ys))
                                              ((gCollect m xs) ++ (gCollect (gNext m (xs ++ [y])) ys)).
Proof.
  generalize dependent xs. generalize dependent y. induction ys using list_r_ind.
  - intros. rewrite app_nil_r. rewrite gCollectNext_last. auto.
  - intros. rewrite app_assoc. rewrite gCollectNext_last.
    unfold gCollect. rewrite IHys. rewrite gCollectNext_last. simpl.
    unfold gCollect.
    rewrite app_assoc. unfold gFinal. repeat rewrite gNext_app. auto.
Qed.

Lemma gCollect_app {A B : Type} (m : Moore A B) (xs ys : list A) (y : A) :
  gCollect m ((xs ++ [y]) ++ ys) = ((gCollect m xs) ++ (gCollect (gNext m (xs ++ [y])) ys)).
Proof.
  pose proof (@gCollectNext_app A B).
  unfold gCollect at 1. Reconstr.scrush.
Qed.

Lemma gCollect_length {A B : Type} (m : Moore A B) (xs : list A) :
  length (gCollect m xs) = S (length xs).
Proof.
  induction xs using list_r_ind.
  - auto.
  - rewrite gCollect_last. rewrite app_length. Reconstr.scrush.
Qed.

Lemma gCollect_last2 {A B : Type} (m : Moore A B) (xs : list A) :
  forall d, last (gCollect m xs) d = gFinal m xs.
Proof.
  intros. induction xs using list_r_ind.
  - auto.
  - rewrite gCollect_last. now rewrite last_nonempty.
Qed.

Lemma gCollect_firstn {A B : Type} (m : Moore A B) (xs : list A) (n : nat) :
  gCollect m (firstn n xs) = firstn (S n) (gCollect m xs).
Proof.
  rewrite <- firstn_skipn with (l := xs) (n := n) at 2.
  destruct (skipn n xs) eqn:E.
  - rewrite app_nil_r. rewrite firstn_all2 with (n := S n). reflexivity.
    rewrite gCollect_length. rewrite firstn_length. lia.
  - replace (a :: l) with ([a] ++ l) by auto. rewrite app_assoc.
    rewrite gCollect_app. rewrite firstn_app.
    assert ((S n) = (length (gCollect m (firstn n xs)))).
    { rewrite gCollect_length.
      pose proof (skipn_nonempty n xs).
      specialize (H ltac:(Reconstr.scrush)).
      rewrite firstn_length.
      rewrite PeanoNat.Nat.min_l by lia. auto.
    }
    replace ((S n - length (gCollect m (firstn n xs)))) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r. rewrite firstn_all2 with (n := S n).
    reflexivity. lia.
Qed.

Lemma gCollect_firstn_last {A B : Type} (m : Moore A B) (xs : list A) (n : nat) :
  forall d, last (firstn (S n) (gCollect m xs)) d = gFinal m (firstn n xs).
Proof.
  pose proof (@gCollect_firstn A B).
  pose proof (@gCollect_last2 A B).
  Reconstr.scrush.
Qed.

Lemma gCollect_prefixes {A B : Type} (m : Moore A B) (xs : list A) :
  gCollect m xs = map (gFinal m) (prefixes xs).
Proof.
  induction xs using list_r_ind.
  - auto.
  - rewrite gCollect_last. rewrite prefixes_app_last. rewrite map_app.
    now rewrite IHxs.
Qed.

Lemma gCollect_prefixes_lastn {A B : Type} (n : nat) (m : Moore A B) (xs : list A) :
  lastn (S n) (gCollect m xs) = map (gFinal m) (lastn (S n) (prefixes xs)).
Proof.
  rewrite gCollect_prefixes. now rewrite map_lastn.
Qed.

(* Some simple machines *)

CoFixpoint mConst {A B : Type} (o : B) : Moore A B := {|
  mOut := o;
  mNext (_ : A) := mConst o;
|}.

(* lifting functions to stateless machines *)
CoFixpoint mLift {A B: Type} (f : A -> B) (init : B) : Moore A B :=
  {|
    mOut := init;
    mNext (a : A) := mLift f (f a)
  |}.

Lemma mLift_correctness_state {A B : Type}: forall (xs : list A) (x : A) (f : A -> B) (init : B),
    gNext (mLift f init) (xs ++ [x]) = mLift f (f x).
Proof.
  intros.
  rewrite gNext_app. generalize dependent x. induction xs using list_r_ind.
  - auto.
  - rewrite gNext_app. Reconstr.scrush.
Qed.

Lemma mLift_correctness_final {A B : Type}: forall (xs : list A) (x : A) (f : A -> B) (init : B),
    gFinal (mLift f init) (xs ++ [x]) = f x.
Proof.
  intros. unfold gFinal. rewrite mLift_correctness_state. auto.
Qed.

(* composition of machines *)

CoFixpoint compose {A B C : Type} (f : Moore A B) (g : Moore B C) (init: C) : Moore A C :=
  {| mOut := init;
     mNext (a : A) := compose (mNext f a) (mNext g (mNextOut f a)) (mNextOut g (mNextOut f a))
  |}.

Notation "f >> g" := (compose f g) (at level 80, no associativity).

Lemma lift_compose_lift_state {A B C : Type} (f : A -> B) (g : B -> C) (xs : list A) (x : A) :
  forall i1 i2 i3, gNext (((mLift f i1) >> (mLift g i2)) i3) (xs ++ [x]) =
                   ((mLift f (f x)) >> (mLift g (g (gFinal (mLift f i1) (xs ++ [x]))))) (g (f x)).
Proof.
  intros.
  unfold gFinal. rewrite gNext_app. rewrite gNext_app. generalize dependent x.
  induction xs using list_r_ind.
  - auto.
  - rewrite gNext_app. rewrite mLift_correctness_state. rewrite IHxs. unfold compose.
    auto.
Qed.

Lemma lift_compose_lift_correctness {A B C : Type} (f : A -> B) (g : B -> C) (xs : list A) (x : A) :
  forall i1 i2 i3, gFinal (((mLift f i1) >> (mLift g i2)) i3) (xs ++ [x]) =
                   (g (f x)).
Proof.
  intros. unfold gFinal. rewrite lift_compose_lift_state. auto.
Qed.


Lemma compose_lift_state {A B C: Type} (m : Moore A B) (g : B -> C) (xs : list A) (x : A):
  forall i1 i2, gNext ((m >> (mLift g i1)) i2) (xs ++ [x]) =
                ((gNext m (xs ++ [x])) >> (mLift g (g (gFinal m (xs ++ [x])))))
                                                        (g (gFinal m (xs ++ [x]))).
Proof.
  intros.
  unfold gFinal. rewrite gNext_app. rewrite gNext_app. generalize dependent x.
  induction xs using list_r_ind.
  - auto.
  - rewrite gNext_app. rewrite gNext_app. rewrite IHxs. unfold compose.
    auto.
Qed.

Lemma compose_lift_correctness {A B C: Type} (m : Moore A B) (g : B -> C) (xs : list A) (x : A):
  forall i1 i2, gFinal ((m >> (mLift g i1)) i2) (xs ++ [x]) = (g (gFinal m (xs ++ [x]))).
Proof.
  intros. unfold gFinal. rewrite compose_lift_state. auto.
Qed.

Lemma lift_compose_state {A B C : Type} (m : Moore B C) (f : A -> B) (xs : list A) (x : A):
  forall i1 i2, gNext (((mLift f i1) >> m) i2) (xs ++ [x]) =
                ((mLift f (f x)) >> (gNext m (map f (xs ++ [x])))) (gFinal m (map f (xs ++ [x]))).
Proof.
  intros.
  unfold gFinal. rewrite gNext_app. rewrite map_app. simpl. rewrite gNext_app. generalize dependent x.
  induction xs using list_r_ind.
  - auto.
  - rewrite map_app. simpl. rewrite gNext_app. rewrite gNext_app. simpl. rewrite IHxs.
    unfold compose. auto.
Qed.

Lemma lift_compose_correctness {A B C : Type} (m : Moore B C) (f : A -> B) (xs : list A) (x : A):
  forall i1 i2, gFinal (((mLift f i1) >> m) i2) (xs ++ [x]) = (gFinal m (map f (xs ++ [x]))).
Proof.
  intros. unfold gFinal. rewrite lift_compose_state. auto.
Qed.

(* Delay Combinator *)

CoFixpoint delayyWith {A B : Type} (init : B) (front back : list B) (m : Moore A B) : Moore A B :=
  {|
   mOut := init;
   mNext (a : A) :=
     (match front with
      | [] => let back' := rev' back in
             match back' with
             | [] => delayyWith (mOut m) [] [] (mNext m a)
             | (b :: bs) => delayyWith b bs [mOut m] (mNext m a)
             end
      | (f :: fs) => delayyWith f fs (mOut m :: back) (mNext m a)
      end
     );
  |}.

Lemma delayyWith_state {A B : Type} (init : B) (inf inb : list B)
      (m : Moore A B) (xs : list A) (x : A):
  forall initSeg, initSeg = [init] ++ inf ++ rev inb ->
  forall k, k = length initSeg ->
  forall str, str = initSeg ++ gCollect m xs ->
  forall lastSeg, lastSeg = lastn k str ->
             exists fr ba ii, [ii] ++ fr ++ rev ba = lastSeg /\
                         k = length lastSeg /\
           gNext (delayyWith init inf inb m) (xs ++ [x]) = delayyWith ii fr ba (gNext m (xs ++ [x])).
Proof.
  generalize dependent init. generalize dependent inb.
  generalize dependent inf. generalize dependent m. generalize dependent x.
  induction xs using list_r_ind.
  - intros. simpl. destruct inf eqn:Einf.
    + destruct inb eqn:Einb.
      * unfold gCollect in H1. subst. simpl in *.
        exists [], [], (mOut m). split; try split; Reconstr.scrush.
      * unfold gCollect in H1. simpl in *. rewrite rev'_rev.
        destruct (rev (b :: l)) eqn:E.
        eapply f_equal in E. rewrite rev_length in E. simpl in E. discriminate.
        exists l0, [mOut m], b0. simpl. split.
        subst. simpl. rewrite app_length. simpl.
        replace (S (length (rev l) + 1)) with (length (rev l) + 2) by lia.
        replace (init :: (rev l ++ [b]) ++ [mOut m]) with
            ([init] ++ (rev l ++ [b]) ++ [mOut m]) by auto.
        rewrite app_assoc. rewrite app_assoc. rewrite <- app_assoc. rewrite <- app_assoc.
        rewrite lastn_app. rewrite app_length. rewrite app_length. simpl.
        replace ((length (rev l) + 2 - (length (rev l) + 2))) with 0 by lia.
        simpl.
        replace ( (length (rev l) + 2) ) with (length (rev l ++ [b; mOut m])) by now rewrite app_length.
        rewrite lastn_all. replace (b0:: l0 ++ [mOut m]) with ([b0] ++ (l0 ++ [mOut m])) by auto.
        rewrite app_assoc. replace ([b0] ++ l0) with (b0 :: l0) by auto. rewrite <- E.
        simpl. rewrite <- app_assoc. reflexivity.
        split. rewrite H2. rewrite H1. rewrite lastn_length.
        rewrite app_length. rewrite <- H0. simpl. lia.
        reflexivity.
    + exists l, (mOut m :: inb), b. unfold gCollect in H1. simpl in H1. split.
      subst. remember ((b :: l) ++ rev inb).
      rewrite app_length. simpl length. rewrite <- app_assoc.
      rewrite lastn_app. rewrite app_length. simpl length.
      replace ((1 + length l0 - (length l0 + 1))) with 0 by lia.
      replace (1 + length l0) with (length l0 + length [mOut m]) by now simpl; lia.
      rewrite <- app_length. rewrite lastn_all. simpl. rewrite Heql0.
      rewrite app_assoc. reflexivity. split.
      rewrite H2. rewrite H1. rewrite lastn_length. rewrite app_length.
      subst; lia.
      reflexivity.
  - intros. specialize (IHxs x m inf inb init initSeg H k H0).
    specialize (IHxs (initSeg ++ gCollect m xs) eq_refl (lastn k (initSeg ++ gCollect m xs)) eq_refl).
    remember (xs ++ [x]) as xs0. destruct IHxs as [fr' [ba' [ii']]]. destruct H3. destruct H4.
    rewrite gNext_app. rewrite H5. rewrite gNext_app.
    destruct fr' eqn:Efr'.
    + destruct ba' eqn:Eba'.
      * exists [], [], (gFinal m xs0). simpl in *.
        rewrite <- H3 in H4. simpl in H4. subst k. rewrite H1 in H2.
        rewrite Heqxs0 in H2. rewrite gCollect_last in H2. rewrite <- Heqxs0 in H2.
        unfold lastn in H2. repeat rewrite rev_app_distr in H2. simpl in H2.
        subst lastSeg. split; auto.
      * destruct (rev (b :: l)) eqn:E.
        eapply f_equal in E. rewrite rev_length in E. simpl in E. discriminate.
        exists l0, [gFinal m xs0], b0. simpl. rewrite rev'_rev. rewrite E.
        subst str. rewrite Heqxs0 in H2. rewrite gCollect_last in H2.
        rewrite <- Heqxs0 in H2. simpl in H3.
        rewrite app_assoc in H2. rewrite lastn_app in H2.
        simpl in H2. destruct k. subst initSeg. rewrite app_length in H0.
        simpl in H0. lia. simpl in H2.
        replace (k - 0) with k in H2 by lia.
        rewrite <- tail_lastn in H2. rewrite <- H3 in H2. simpl in H2.
        subst lastSeg. split. Reconstr.scrush.
        split; auto.
        replace (b0 :: l0 ++ lastn (S k) [gFinal m xs0])
          with ((b0::l0) ++ lastn (S k) [gFinal m xs0]) by auto.
        rewrite app_length. replace (b0 :: l0) with (tl (ii' :: b0 :: l0)) by auto.
        rewrite H3. rewrite tl_length. rewrite <- H4. simpl. rewrite lastn_length.
        simpl; lia.
        rewrite app_length. lia.
    + exists l, (gFinal m xs0 :: ba'), b. simpl.
      subst str. replace (b :: l ++ rev ba' ++ [gFinal m xs0] )
                         with ((b :: l) ++ (rev ba' ++ [gFinal m xs0]))  by auto.
      rewrite app_assoc. remember ((b :: l) ++ rev ba').
      rewrite Heqxs0 in H2. rewrite gCollect_last in H2. rewrite <- Heqxs0 in H2.
      rewrite app_assoc in H2. remember (initSeg ++ gCollect m xs).
      rewrite lastn_app in H2. simpl in H2.
      destruct k. subst initSeg. rewrite app_length in H0.
      simpl in H0. lia. simpl in H2.
      replace (k - 0) with k in H2 by lia.
      rewrite <- tail_lastn in H2. rewrite <- H3 in H2. simpl in H2.
      unfold lastn in H2. simpl in H2. rewrite firstn_nil in H2. simpl in H2.
      subst lastSeg. split. auto. split. simpl in H3.
      replace (l0) with (tl (ii' :: l0)) by auto. rewrite app_length. rewrite tl_length.
      rewrite H3. rewrite <- H4. simpl. lia.
      auto. rewrite Heql1. rewrite app_length. lia.
Qed.

Lemma delayyWith_final {A B : Type} (init : B) (inf inb : list B)
      (m : Moore A B) (xs : list A) (x : A):
  forall d, gFinal (delayyWith init inf inb m) (xs ++ [x]) =
       hd d (lastn (length ([init] ++ inf ++ rev inb)) (([init] ++ inf ++ rev inb) ++ gCollect m xs)).
Proof.
  intros.
  pose proof (delayyWith_state init inf inb m xs x).
  pose (initSeg := [init] ++ inf ++ rev inb).
  pose (k := length initSeg). pose (str := initSeg ++ gCollect m xs).
  pose (lastSeg := lastn k str).
  specialize (H initSeg eq_refl k eq_refl str eq_refl lastSeg eq_refl).
  destruct H as [fr [ba [ii]]]. destruct H. destruct H0.
  unfold gFinal. Reconstr.scrush.
Qed.


(* pointwise binary operations *)

CoFixpoint mBinOp {A B C D: Type} (op : B -> C -> D) (m1: Moore A B) (m2 : Moore A C) : Moore A D :=
  {|
  mOut := op (mOut m1) (mOut m2);
  mNext (a : A) := mBinOp op (mNext m1 a) (mNext m2 a)
  |}.

Lemma mBinOp_state {A B C D: Type} (op : B -> C -> D) (m1: Moore A B) (m2 : Moore A C) (xs : list A) :
  gNext (mBinOp op m1 m2) xs = mBinOp op (gNext m1 xs) (gNext m2 xs).
Proof.
  induction xs using list_r_ind.
  - auto.
  - repeat rewrite gNext_app. rewrite IHxs. Reconstr.scrush.
Qed.

Lemma mBinOp_final {A B C D: Type} (op : B -> C -> D) (m1: Moore A B) (m2 : Moore A C) (xs : list A) :
  gFinal (mBinOp op m1 m2) xs = op (gFinal m1 xs) (gFinal m2 xs).
Proof.
  pose proof (@mBinOp_state A B C D). unfold gFinal. Reconstr.scrush.
Qed.

(* Running Aggregates *)

Section mFold.

  Variable (B : Type).
  Context {monoid_B : Monoid B}.


  CoFixpoint mFoldAux {A : Type} (m : Moore A B) (st : B) : Moore A B :=
  {| mOut := st;
     mNext (a : A) := mFoldAux (mNext m a) (op st (mNextOut m a))
  |}.

  Definition mFold {A : Type} (m : Moore A B) :=
    mFoldAux m (mOut m).

  Lemma mFold_state {A : Type} (m : Moore A B) (xs : list A) :
    gNext (mFold m) xs = mFoldAux (gNext m xs) (fold_left op (gCollect m xs) unit).
  Proof.
    unfold mFold. induction xs using list_r_ind.
    - Reconstr.scrush.
    - rewrite gNext_app. rewrite IHxs.
      rewrite gNext_app. simpl.
      rewrite gCollect_last. rewrite fold_left_app.
      unfold gFinal. rewrite gNext_app. simpl.
      now unfold mNextOut.
  Qed.

  Lemma mFold_final {A : Type} (m : Moore A B) (xs : list A) :
    gFinal (mFold m) xs = fold_left op (gCollect m xs) unit.
  Proof.
    unfold gFinal. rewrite mFold_state. auto.
  Qed.

  (* sliding window aggregate *)

  Record aggQueue : Type :=
    {
       ff : list (B * B);
       rr : list (B * B);
    }.

  Definition lenQ (q : aggQueue) := length (ff q) + length (rr q).

  Definition contentsQ (q : aggQueue) :=  unzip_snd (ff q) ++ rev (unzip_snd (rr q)).
  Definition contentsff (q : aggQueue) := unzip_snd (ff q).
  Definition contentsrr (q : aggQueue) := unzip_snd (rr q).
  Definition aggsff (q : aggQueue) := unzip_fst (ff q).
  Definition aggsrr (q : aggQueue) := unzip_fst (rr q).

  Definition aggsffInv (q : aggQueue) : Prop :=
    forall i, hd unit (lastn i (aggsff q)) = finite_op B (lastn i (contentsff q)).
  Definition aggsrrInv (q : aggQueue) : Prop :=
    forall i, hd unit (lastn i (aggsrr q)) = finite_op B (rev (lastn i (contentsrr q))).

  Definition aggrr (q : aggQueue) : B :=
    (match (rr q) with
            | [] => unit
            | ((xa, x) :: _) => xa
            end
    ).

  Lemma aggrr_alternate :
    forall q, aggrr q = hd unit (aggsrr q).
  Proof.
    destruct q; Reconstr.scrush.
  Qed.



  Definition aggff (q : aggQueue) : B :=
    (match (ff q) with
            | [] => unit
            | ((ya, y) :: _) => ya
            end
    ).

  Lemma aggff_alternate :
    forall q, aggff q = hd unit (aggsff q).
  Proof.
    destruct q; Reconstr.scrush.
  Qed.


  Definition aggOut (q : aggQueue) : B :=
    op (aggff q) (aggrr q).

  Definition aggInv (q : aggQueue) : Prop :=
    aggOut q = finite_op B (contentsQ q).

  Lemma aggInv_aggsrrInv_aggsffInv (q : aggQueue) :
    aggsffInv q -> aggsrrInv q -> aggInv q.
  Proof.
    unfold aggsffInv. unfold aggsrrInv. unfold aggInv. unfold aggOut.
    rewrite aggrr_alternate. rewrite aggff_alternate.
    unfold aggsff. unfold aggsrr. unfold contentsff. unfold contentsrr.
    unfold contentsQ.
    intros. specialize (H (length (ff q))). rewrite <- unzip_fst_length in H at 1.
    rewrite <- unzip_snd_length in H. repeat rewrite lastn_all in H.
    specialize (H0 (length (rr q))). rewrite <- unzip_fst_length in H0 at 1.
    rewrite <- unzip_snd_length in H0. repeat rewrite lastn_all in H0.
    rewrite H. rewrite H0. now rewrite finite_op_app.
  Qed.

  Definition aggStep (q : aggQueue) : aggQueue :=
    match (rr q) with
    | [] => q
    | ((ra, r) :: rs) =>
      {|
        ff := (op r (aggff q), r) :: (ff q);
        rr := rs;
      |}
    end.

  Lemma aggStep_length :
    forall q, lenQ (aggStep q) = lenQ q.
  Proof.
    intros. unfold lenQ. destruct (rr q) eqn:E.
    + unfold aggStep. rewrite E. now rewrite E.
    + unfold aggStep. rewrite E. simpl. destruct p. simpl. lia.
  Qed.


  Function aggFlip (qq : aggQueue) {measure (fun qq => length (rr qq)) qq} : aggQueue :=
    match (rr qq) with
    | [] => qq
    | (r :: rs) =>
      aggFlip (aggStep qq)
    end.
  unfold aggStep. Reconstr.scrush.
  Defined.

  Lemma aggFlip_length :
    forall q, lenQ (aggFlip q) = lenQ q.
  Proof.
    assert (forall l, (forall q, rr q = l -> lenQ (aggFlip q) = lenQ q)).
    induction l.
    - intros. rewrite aggFlip_equation. now rewrite H.
    - intros. rewrite aggFlip_equation. rewrite H. rewrite IHl.
      now rewrite aggStep_length. unfold aggStep. rewrite H.
      Reconstr.scrush.
    - Reconstr.scrush.
  Qed.

  Lemma aggFlip_rr_empty :
    forall q, rr (aggFlip q) = [].
  Proof.
    assert (forall l, (forall q, rr q = l -> rr (aggFlip q) = [])).
    induction l.
    - intros. rewrite aggFlip_equation. now rewrite H.
    - intros. rewrite aggFlip_equation. rewrite H. rewrite IHl.
      reflexivity. unfold aggStep. rewrite H. Reconstr.scrush.
    - Reconstr.scrush.
  Qed.

  Lemma aggFlip_ff_nonEmpty :
    forall q, ff (aggFlip q) = [] <-> ff q = [] /\ rr q = [].
  Proof.
    intros. pose proof (aggFlip_length q).
    unfold lenQ in H. rewrite aggFlip_rr_empty in H. simpl in H.
    rewrite Nat.add_0_r in H. pose proof (length_zero_iff_nil).
    split.
    - intros. eapply f_equal in H1. rewrite H1 in H. simpl in H.
      assert (length (ff q) = 0) by lia.
      assert (length (rr q) = 0) by lia.
      Reconstr.scrush.
    - intros []. Reconstr.scrush.
  Qed.

  Lemma aggFlip_contentsrr_contentsff :
    forall q, contentsff (aggFlip q) = rev (contentsrr q) ++ contentsff q.
  Proof.
    assert (forall l, (forall q, rr q = l -> contentsff (aggFlip q) = rev (contentsrr q) ++ contentsff q)).
    induction l.
    - intros. rewrite aggFlip_equation. rewrite H. unfold contentsrr. rewrite H. reflexivity.
    - intros. rewrite aggFlip_equation. rewrite H. unfold aggStep. rewrite H.
      destruct a. rewrite IHl by auto. simpl. unfold contentsff. unfold contentsrr.
      simpl. rewrite H. simpl. Reconstr.scrush.
    - Reconstr.scrush.
  Qed.

  Definition aggEnQ (new : B) (q : aggQueue) : aggQueue :=
      {|
      ff := ff q;
      rr := (((op (aggrr q) new), new) :: rr q);
      |}.

  Lemma aggEnQ_contentsQ :
    forall x q, contentsQ (aggEnQ x q) = contentsQ q ++ [x].
  Proof.
    intros. unfold aggEnQ. unfold contentsQ.
    Reconstr.scrush.
  Qed.

  Lemma aggEnQ_length :
    forall x q, lenQ (aggEnQ x q) = S (lenQ q).
  Proof.
    intros. unfold aggEnQ. unfold lenQ. simpl. lia.
  Qed.


  Definition aggDQ (q : aggQueue) : aggQueue :=
      match (ff q) with
      | [] => let newQ := (aggFlip q) in
             match (ff newQ) with
             | [] => newQ
             | (f :: fs) => {| ff := fs; rr := rr newQ|}
             end
      | (f :: fs) => {| ff := fs; rr := rr q|}
      end.

  Lemma aggDQ_contentsQ :
    forall q, contentsQ (aggDQ q) = tl (contentsQ q).
  Proof.
    intros. unfold aggDQ.
    destruct (ff q) eqn:E.
    - destruct (ff (aggFlip q)) eqn:F.
      + rewrite aggFlip_ff_nonEmpty in F.
        Reconstr.ryelles4 Reconstr.Empty Reconstr.Empty.
      + pose proof (aggFlip_contentsrr_contentsff q).
        unfold contentsff in *. unfold contentsrr in *. unfold contentsQ.
        simpl. rewrite E in *. rewrite F in *. simpl in *.
        rewrite app_nil_r in H. rewrite <- H. simpl.
        rewrite aggFlip_rr_empty. Reconstr.scrush.
    - unfold contentsQ. now rewrite E.
  Qed.

  Lemma aggDQ_length :
    forall q, lenQ (aggDQ q) = pred (lenQ q).
  Proof.
    intros. destruct (ff q) eqn:E; unfold aggDQ; rewrite E.
    - destruct (ff (aggFlip q)) eqn:F.
      + rewrite aggFlip_ff_nonEmpty in F.
        Reconstr.ryelles4 Reconstr.Empty Reconstr.Empty.
      + pose proof (aggFlip_length q). unfold lenQ in H.
        unfold lenQ. Reconstr.rsimple Reconstr.Empty Reconstr.Empty.
    - unfold lenQ. Reconstr.scrush.
  Qed.

  Lemma aggEnQ_aggsrrInv (q : aggQueue) :
    forall x, aggsrrInv q -> aggsrrInv (aggEnQ x q).
  Proof.
    unfold aggsrrInv. unfold aggsrr. unfold contentsrr.
    intros. unfold aggEnQ. simpl.
    remember (unzip_fst (rr q)) as l1. remember (unzip_snd (rr q)) as l2.
    assert (length l1 = length l2).
    { rewrite Heql1. rewrite Heql2. now rewrite unzip_fst_snd_length. }
    destruct (PeanoNat.Nat.le_gt_cases i (length l1)).
    - assert (i < length (op (aggrr q) x :: l1)) by now simpl; lia.
      assert (i < length (x :: l2)) by now simpl; lia.
      rewrite <- lastn_tail by lia. simpl. rewrite <- lastn_tail with (xs := (x :: l2)) by lia.
      auto.
    - assert (i >= length (op (aggrr q) x :: l1)) by now simpl; lia.
      assert (i >= length (x :: l2)) by now simpl; lia.
      rewrite lastn_all2 by lia. rewrite lastn_all2 by lia.
      simpl. specialize (H (length l1)). rewrite lastn_all in H.
      rewrite H0 in H. rewrite lastn_all in H.
      rewrite <- finite_op_app. rewrite aggrr_alternate. unfold aggsrr.
      rewrite <- Heql1. rewrite H. now rewrite finite_op_singleton.
  Qed.

  Lemma aggEnQ_aggsffInv (q : aggQueue) :
    forall x, aggsffInv q -> aggsffInv (aggEnQ x q).
  Proof.
    Reconstr.scrush.
  Qed.

  Lemma aggDQ_aggsrrInv (q : aggQueue) :
    aggsrrInv q -> aggsrrInv (aggDQ q).
  Proof.
    unfold aggsrrInv.
    intros. destruct (ff q) eqn:E.
    - unfold aggDQ. rewrite E. remember (aggFlip q).
      destruct (ff a) eqn:F.
      + rewrite Heqa in F. rewrite aggFlip_ff_nonEmpty in F. destruct F.
        rewrite aggFlip_equation in Heqa. rewrite H1 in Heqa. Reconstr.scrush.
      + unfold aggsrr in *. unfold contentsrr in *. simpl.
        rewrite Heqa. rewrite aggFlip_rr_empty. Reconstr.scrush.
    - unfold aggDQ. rewrite E. Reconstr.scrush.
  Qed.

  Lemma aggStep_aggsffInv (q : aggQueue) :
    aggsffInv q -> aggsffInv (aggStep q).
  Proof.
    unfold aggsffInv. unfold contentsff. unfold aggsff.
    remember (unzip_fst (ff q)) as l1. remember (unzip_snd (ff q)) as l2.
    assert (length l1 = length l2).
    { rewrite Heql1. rewrite Heql2. now rewrite unzip_fst_snd_length. }
    intros. destruct (rr q) eqn:E.
    - unfold aggStep. rewrite E. Reconstr.scrush.
    - unfold aggStep. destruct p eqn:F. rewrite E. simpl.
      destruct (PeanoNat.Nat.le_gt_cases i (length l1)).
      +  rewrite <- Heql1.
         assert (i < length (op b0 (aggff q) :: l1)) by now simpl; lia.
         rewrite <- Heql2.
         assert (i < length (b0 :: l2)) by now simpl; lia.
         rewrite <- lastn_tail by lia. simpl. rewrite <- lastn_tail with (xs := (b0 :: l2)) by lia.
         auto.
      + rewrite <- Heql1.
         assert (i >= length (op b0 (aggff q) :: l1)) by now simpl; lia.
         rewrite <- Heql2.
         assert (i >= length (b0 :: l2)) by now simpl; lia.
         rewrite lastn_all2 by lia. rewrite lastn_all2 by lia.
         simpl. specialize (H0 (length l1)). rewrite lastn_all in H0.
         rewrite H in H0. rewrite lastn_all in H0. unfold finite_op.
         simpl. rewrite op_unit_l. rewrite aggff_alternate. unfold aggsff.
         rewrite <- Heql1. rewrite H0. now rewrite finite_op_fold_left.
  Qed.

  Lemma aggFlip_aggsffInv (q : aggQueue) :
    aggsffInv q -> aggsffInv (aggFlip q).
  Proof.
    assert (forall l, (forall q, rr q = l -> aggsffInv q -> aggsffInv (aggFlip q))).
    induction l.
    - intros. Reconstr.ryelles4 Reconstr.Empty Reconstr.Empty.
    - intros. rewrite aggFlip_equation. rewrite H. apply IHl.
      Reconstr.ryelles4 Reconstr.Empty Reconstr.Empty.
      now apply aggStep_aggsffInv.
    - Reconstr.scrush.
  Qed.

  Lemma aggDQ_aggsffInv (q : aggQueue) :
    aggsffInv q -> aggsffInv (aggDQ q).
  Proof.
    intros XX. generalize XX.
    unfold aggsffInv. unfold aggsff. unfold contentsff.
    remember (unzip_fst (ff q)) as l1. remember (unzip_snd (ff q)) as l2.
    assert (length l1 = length l2).
    { rewrite Heql1. rewrite Heql2. now rewrite unzip_fst_snd_length. }
    unfold aggDQ. destruct (ff q) eqn:E.
    - destruct (ff (aggFlip q)) eqn:F.
      + rewrite aggFlip_ff_nonEmpty in F. destruct F.
        intros. rewrite aggFlip_equation. rewrite H1. rewrite E.
        Reconstr.scrush.
      + intros. simpl. apply aggFlip_aggsffInv in XX.
        unfold aggsffInv in XX. unfold aggsff in XX. unfold contentsff in XX.
        rewrite F in XX. clear XX0. simpl in XX.
        destruct (PeanoNat.Nat.le_gt_cases i (length l)).
        * specialize (XX i).
        assert (i < length (fst p :: unzip_fst l)) by now simpl ; rewrite unzip_fst_length ; lia.
        assert (i < length (snd p :: unzip_snd l)) by now simpl ; rewrite unzip_snd_length ; lia.
        rewrite <- lastn_tail in XX by auto.
        rewrite <- lastn_tail with (xs := (snd p :: unzip_snd l)) in XX by auto.
        auto.
        * rewrite lastn_all2. rewrite lastn_all2. specialize (XX (length l)).
        rewrite <- unzip_fst_length in XX at 1. rewrite <- unzip_snd_length in XX.
        rewrite <- lastn_tail in XX by now simpl; lia.
        rewrite <- lastn_tail with (xs := (snd p :: unzip_snd l)) in XX by now simpl; lia.
        simpl in XX. now repeat rewrite lastn_all in XX.
        rewrite unzip_snd_length; lia.
        rewrite unzip_fst_length; lia.
    - simpl in *. intros.
      destruct (PeanoNat.Nat.le_gt_cases i (length l)).
      + rewrite Heql1 in XX0. rewrite Heql2 in XX0.
        specialize (XX0 i).
        assert (i < length (fst p :: unzip_fst l)) by now simpl ; rewrite unzip_fst_length ; lia.
        assert (i < length (snd p :: unzip_snd l)) by now simpl ; rewrite unzip_snd_length ; lia.
        rewrite <- lastn_tail in XX0 by auto.
        rewrite <- lastn_tail with (xs := (snd p :: unzip_snd l)) in XX0 by auto.
        auto.
      + rewrite lastn_all2. rewrite lastn_all2. specialize (XX0 (length l)).
        rewrite Heql2 in XX0. rewrite Heql1 in XX0.
        rewrite <- unzip_fst_length in XX0 at 1. rewrite <- unzip_snd_length in XX0.
        rewrite <- lastn_tail in XX0 by now simpl; lia.
        rewrite <- lastn_tail with (xs := (snd p :: unzip_snd l)) in XX0 by now simpl; lia.
        simpl in XX0. now repeat rewrite lastn_all in XX0.
        rewrite unzip_snd_length; lia.
        rewrite unzip_fst_length; lia.
  Qed.

  Definition aggCycle (x : B) (q : aggQueue) :=
    aggDQ (aggEnQ x q).

  Lemma aggCycle_length :
    forall x q, lenQ (aggCycle x q) = lenQ q.
  Proof.
    unfold aggCycle. intros. rewrite aggDQ_length.
    rewrite aggEnQ_length. lia.
  Qed.

  Lemma aggCycle_contentsQ :
    forall x q, contentsQ (aggCycle x q) = tl (contentsQ q ++ [x]).
  Proof.
    unfold aggCycle.
    pose proof aggEnQ_contentsQ. pose proof aggDQ_contentsQ.
    Reconstr.scrush.
  Qed.

  Lemma aggCycle_aggsffInv :
    forall x q, aggsffInv q -> aggsffInv (aggCycle x q).
  Proof.
    intros. unfold aggCycle. apply aggDQ_aggsffInv. now apply aggEnQ_aggsffInv.
  Qed.

  Lemma aggCycle_aggsrrInv :
    forall x q, aggsrrInv q -> aggsrrInv (aggCycle x q).
  Proof.
    intros. unfold aggCycle. apply aggDQ_aggsrrInv. now apply aggEnQ_aggsrrInv.
  Qed.

  Definition initAggQ (n : nat) : aggQueue :=
    {| ff := repeat' (unit, unit) (S n)
     ; rr := [] |}.

  Lemma initAggQ_aggsffInv :
    forall n, aggsffInv (initAggQ n).
  Proof.
    unfold initAggQ. unfold aggsffInv.
    unfold aggsff. unfold contentsff.
    induction n.
    - rewrite repeat_repeat'. simpl. destruct i.
      + auto.
      + Reconstr.scrush.
    - intros. rewrite repeat_repeat' in *. simpl. simpl in IHn.
      destruct (PeanoNat.Nat.lt_ge_cases i (length (unit :: unit :: unzip_fst (repeat (unit, unit) n)))).
      rewrite <- lastn_tail. simpl. rewrite <- lastn_tail with (xs := (unit :: unit :: unzip_snd (repeat (unit, unit) n))). simpl. auto.
      simpl in H. simpl. rewrite unzip_fst_snd_length. lia.
      simpl in H. simpl. lia.
      rewrite lastn_all2. rewrite lastn_all2.
      specialize (IHn (length (unit :: unzip_snd (repeat (unit, unit) n)))).
      rewrite lastn_all in IHn.
      replace ((length (unit :: unzip_snd (repeat (unit, unit) n)))) with
          (length (unit :: unzip_fst (repeat (unit, unit) n))) in IHn by now simpl; rewrite unzip_fst_snd_length; lia. rewrite lastn_all in IHn. Reconstr.scrush.
      simpl in *. rewrite unzip_fst_snd_length. lia.
      simpl in *. lia.
  Qed.

  Lemma initAggQ_aggsrrInv:
    forall n, aggsrrInv (initAggQ n).
  Proof.
    intros. unfold initAggQ. unfold aggsrrInv.
    unfold aggsrr. unfold contentsrr.
    Reconstr.scrush.
  Qed.

  CoFixpoint mWinFoldAux {A : Type} (qq : aggQueue) (m : Moore A B) : Moore A B :=
    {|
    mOut := op (aggOut qq) (mOut m);
    mNext (a : A) := mWinFoldAux (aggCycle (mOut m) qq) (mNext m a);
    |}.

  Definition mWinFold {A : Type} (m : Moore A B) (n : nat) : Moore A B :=
    mWinFoldAux (initAggQ n) m.

  Lemma mWinFold_state {A : Type} (m : Moore A B) (n : nat) (xs : list A) (x : A) :
    exists qq, gNext (mWinFold m n) (xs ++ [x]) = mWinFoldAux qq (gNext m (xs ++ [x]))
          /\ contentsQ qq = lastn (S n) (repeat unit (S n) ++ gCollect m xs)
          /\ aggsffInv qq
          /\ aggsrrInv qq.
  Proof.
    generalize dependent x. induction xs using list_r_ind.
    - intros. simpl. exists ((aggCycle (mOut m) (initAggQ n))).
      split. auto.
      rewrite aggCycle_contentsQ. simpl. unfold initAggQ at 1.
      rewrite repeat_repeat'. simpl. rewrite unzip_snd_repeat.
      rewrite app_nil_r. unfold gCollect. simpl.
      rewrite <- lastn_tail. simpl. rewrite lastn_all2. split. reflexivity.
      split. apply aggCycle_aggsffInv. apply initAggQ_aggsffInv.
      apply aggCycle_aggsrrInv. apply initAggQ_aggsrrInv.
      rewrite app_length. rewrite repeat_length. simpl. lia.
      simpl. rewrite app_length. rewrite repeat_length. simpl. lia.
    - intros. specialize (IHxs x). destruct IHxs as [qq0]. destruct H as [H1 [H2 [H3 H4]]].
      remember (xs ++ [x]) as xs0.
      exists (aggCycle (gFinal m xs0) qq0).
      rewrite gNext_app. rewrite H1. simpl.
      unfold gFinal. rewrite gNext_app. simpl.
      split. auto. split.
      rewrite aggCycle_contentsQ. rewrite H2.
      rewrite Heqxs0. rewrite gCollect_last. unfold gFinal.
      assert (unit :: repeat unit n ++ gCollect m xs ++ [mOut (gNext m (xs ++ [x]))]
              = (unit :: repeat unit n ++ gCollect m xs) ++ [mOut (gNext m (xs ++ [x]))])
        by Reconstr.scrush.
      rewrite H. clear H.
      replace (unit :: repeat unit n ++ gCollect m xs) with
          (repeat unit (S n) ++ gCollect m xs) by auto.
      remember (repeat unit (S n) ++ gCollect m xs).
      rewrite lastn_app. simpl.
      rewrite tl_app. rewrite tail_lastn.
      Reconstr.rsimple Reconstr.Empty Reconstr.Empty.
      rewrite Heql. rewrite app_length. rewrite repeat_length. lia.
      rewrite Heql. unfold not. intros. eapply f_equal in H. rewrite lastn_length in H.
      rewrite app_length in H. rewrite repeat_length in H. simpl in H. lia.
      split.
      now apply aggCycle_aggsffInv.
      now apply aggCycle_aggsrrInv.
  Qed.

  Lemma mWinFold_final1 {A : Type} (m : Moore A B) (n : nat) (xs : list A) (x : A) :
    length xs < (S n)
    -> gFinal (mWinFold m n) (xs ++ [x]) = finite_op B (gCollect m (xs ++ [x])).
  Proof.
    intros. unfold gFinal. pose proof (mWinFold_state m n xs x). destruct H0 as [qq].
    destruct H0 as [H1 [H2 [H3 H4]]].
    rewrite H1. pose proof (aggInv_aggsrrInv_aggsffInv qq H3 H4).
    unfold aggInv in H0. simpl. rewrite H0. rewrite H2.
    rewrite lastn_app. rewrite gCollect_length.
    rewrite lastn_repeat. rewrite <- finite_op_app.
    rewrite lastn_all2 by now rewrite gCollect_length; lia.
    rewrite finite_op_repeat_unit. rewrite op_unit_l.
    rewrite gCollect_last. rewrite <- finite_op_app.
    unfold gFinal. now rewrite finite_op_singleton.
  Qed.

  Lemma mWinFold_final2 {A : Type} (m : Moore A B) (n : nat) (xs : list A) (x : A) :
    length xs >= (S n)
    -> gFinal (mWinFold m n) (xs ++ [x]) = finite_op B (lastn (S (S n)) (gCollect m (xs ++ [x]))).
  Proof.
    intros. unfold gFinal. pose proof (mWinFold_state m n xs x). destruct H0 as [qq].
    destruct H0 as [H1 [H2 [H3 H4]]].
    rewrite H1. pose proof (aggInv_aggsrrInv_aggsffInv qq H3 H4).
    unfold aggInv in H0. simpl. rewrite H0. rewrite H2.
    rewrite lastn_app. rewrite gCollect_length.
    replace (S n - S (length xs)) with 0 by lia. simpl.
    rewrite gCollect_last. rewrite lastn_app. simpl.
    rewrite <- finite_op_app. sauto.
  Qed.

  Lemma mWinFold_final3  {A : Type} (m : Moore A B) (n : nat) (xs : list A) (x : A) :
    gFinal (mWinFold m n) (xs ++ [x]) = finite_op B (lastn (S (S n)) (gCollect m (xs ++ [x]))).
  Proof.
    destruct (PeanoNat.Nat.lt_ge_cases (length xs) (S n)).
    - rewrite mWinFold_final1 by assumption.
      now rewrite lastn_all2 by now rewrite gCollect_length; rewrite app_length; simpl; lia.
    - Reconstr.reasy (@mFold.mWinFold_final2) (@Coq.Init.Peano.ge).
  Qed.

  Lemma aggOut_initAggQ :
    forall n, aggOut (initAggQ n) = unit.
  Proof.
    unfold aggOut. unfold aggff. unfold aggrr. simpl. intros.
    rewrite repeat_repeat'.
    now rewrite op_unit_r.
  Qed.

  Lemma mWinFold_final  {A : Type} (m : Moore A B) (n : nat) (xs : list A) :
    gFinal (mWinFold m n) xs = finite_op B (lastn (S (S n)) (gCollect m xs)).
  Proof.
    destruct xs using list_r_ind.
    - unfold gFinal. unfold gCollect. unfold lastn. simpl. rewrite finite_op_singleton.
      rewrite aggOut_initAggQ. now rewrite op_unit_l.
    - apply mWinFold_final3.
  Qed.

End mFold.

