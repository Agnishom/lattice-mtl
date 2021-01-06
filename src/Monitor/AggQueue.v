From NonEmptyList Require Import NonEmptyList.
From Algebra Require Import Monoid.
Require Import Coq.Lists.List.

Import NonEmptyNotations.
Import ListNotations.

Require Import Lia.
From Lemmas Require Import Lemmas.
Require Import Recdef.
Require Import FunInd.

Require Import Mealy.


Section aggQueue.

  Variable (B : Type).
  Context {monoid_B : Monoid B}.

  Record aggQueue : Type :=
    {
    new : list B;
    newAgg : B;
    oldAggs : list B;
    }.

  Definition agg (q : aggQueue) :=
    match oldAggs q with
    | [] => (newAgg q)
    | (x :: xs) => op x (newAgg q)
    end.

  Definition new_inv (news : list B) (q : aggQueue) :=
    new q = rev news.
  Definition newAgg_inv (q : aggQueue) :=
    newAgg q = finite_op _ (rev (new q)).
  Definition oldAggs_inv (olds : list B) (q : aggQueue) :=
    length (oldAggs q) = length olds
    /\ forall i , nth i (oldAggs q) unit = finite_op _ (skipn i olds).
  Definition aggQueue_inv (l : list B) (q : aggQueue) :=
    exists olds news,
      olds ++ news = l
      /\ new_inv news q
      /\ newAgg_inv q
      /\ oldAggs_inv olds q.
  Definition agg_inv (l : list B) (q : aggQueue) :=
    agg q = finite_op _ l.

  Lemma aggQueue_agg_inv l q :
    aggQueue_inv l q -> agg_inv l q.
  Proof.
    intros. destruct H as [olds [news [Hl [H1 [H2 H3]]]]].
    unfold new_inv in H1.
    unfold newAgg_inv in H2.
    unfold oldAggs_inv in H3. destruct H3 as [H3 H4].
    unfold agg_inv. unfold agg.
    destruct olds.
    - simpl in *. assert (oldAggs q = []).
      { destruct (oldAggs q); auto. simpl in H3. lia. }
      rewrite H. subst l. rewrite H2.
      eapply f_equal in H1. rewrite rev_involutive in H1.
      now rewrite <- H1.
    - destruct (oldAggs q); [simpl in H3; lia | ].
      specialize (H4 0). simpl in H4.
      rewrite H2. rewrite H1. simpl_list.
      rewrite H4. rewrite finite_op_app.
      now rewrite Hl.
  Qed.


  Definition aggEnqueue (n : B) (q : aggQueue) : aggQueue :=
    {|
    new := n :: (new q);
    newAgg := op (newAgg q) n;
    oldAggs := oldAggs q;
    |}.

  Lemma enqueue_new_inv news q :
    new_inv news q
    -> forall n, new_inv (news ++ [n]) (aggEnqueue n q).
  Proof.
    intros.
    unfold new_inv in *.
    destruct q. simpl in *.
    simpl_list. now rewrite H.
  Qed.

  Lemma enqueue_newAgg_inv q :
    newAgg_inv q
    -> forall n, newAgg_inv (aggEnqueue n q).
  Proof.
    unfold newAgg_inv in *.
    destruct q.
    simpl.
    intros. rewrite <- finite_op_app.
    rewrite <- H.
    now rewrite finite_op_singleton.
  Qed.

  Lemma enqueue_oldAggs_inv olds q :
    oldAggs_inv olds q
    -> forall n, oldAggs_inv olds (aggEnqueue n q).
  Proof.
    unfold oldAggs_inv. destruct q.
    simpl. firstorder.
  Qed.

  Lemma enqueue_aggQueue_inv l q :
    aggQueue_inv l q
    -> forall n, aggQueue_inv (l ++ [n]) (aggEnqueue n q).
  Proof.
    unfold aggQueue_inv. intros.
    destruct H as [olds [news [H1 [H2 [H3 H4]]]]].
    exists olds, (news ++ [n]).
    split.
    - rewrite <- H1. now apply app_assoc.
    - split.
      -- now apply enqueue_new_inv.
      -- split.
         --- now apply enqueue_newAgg_inv.
         --- now apply enqueue_oldAggs_inv.
  Qed.


  Definition aggStep (q : aggQueue) : aggQueue :=
    match (new q) with
    | [] => q
    | (n :: ns) => {| new := ns;
                    newAgg := unit;
                    oldAggs := op n (hd unit (oldAggs q)) :: (oldAggs q)
                 |}
    end.

  Lemma aggStep_new_inv ns n q :
    new_inv (ns ++ [n]) q
    -> new_inv ns (aggStep q).
  Proof.
    unfold new_inv. destruct q. unfold aggStep.
    simpl. intros. destruct new0.
    eapply f_equal in H. rewrite rev_length in H.
    rewrite app_length in H. simpl in H. lia.
    rewrite rev_app_distr in H. simpl in H.
    inversion H. auto.
  Qed.

  Lemma aggStep_oldAggs_inv ns n olds q :
    new_inv (ns ++ [n]) q
    -> oldAggs_inv olds q
    -> oldAggs_inv (n :: olds) (aggStep q).
  Proof.
    unfold new_inv.
    unfold oldAggs_inv.
    intros. destruct H0 as [H1 H2].
    destruct q eqn:Eq. simpl in *.
    assert (length (oldAggs (aggStep q)) = S (length olds)).
    { unfold aggStep. rewrite Eq. simpl.
      destruct new0.
      { eapply f_equal in H. rewrite rev_length in H.
        rewrite app_length in H. simpl in H. lia. }
      simpl. lia. }
    split.
    - simpl. rewrite <- Eq. lia.
    - rewrite <- Eq. intros. rewrite rev_app_distr in H.
      simpl in H.
      destruct i.
      + rewrite Eq. unfold aggStep. simpl.
        subst new0. simpl. replace (n :: olds) with ([n] ++ olds) by auto.
        rewrite <- finite_op_app. rewrite finite_op_singleton.
        f_equal. specialize (H2 0). simpl in H2. rewrite <- H2.
        unfold nth. unfold hd. destruct oldAggs0; auto.
      + simpl. unfold aggStep. rewrite Eq. subst new0. simpl.
        auto.
  Qed.


  Definition aggLength q : nat :=
    length (new q) + length (oldAggs q).

  Function aggFlip (q : aggQueue) {measure (fun q => length (new q)) q} : aggQueue :=
    match (new q) with
    | [] => q
    | (r :: rs) =>
      aggFlip (aggStep q)
    end.
  unfold aggStep. intros. rewrite teq. auto.
  Defined.

  Lemma aggFlip_new_empty q :
    new (aggFlip q) = [].
  Proof.
    destruct q.
    revert newAgg0 oldAggs0.
    induction new0.
    - auto.
    - intros. rewrite aggFlip_equation.
      simpl. unfold aggStep. simpl. auto.
  Qed.

  Lemma aggFlip_new_inv q :
    new_inv [] (aggFlip q).
  Proof.
    unfold new_inv. pose proof (aggFlip_new_empty q).
    auto.
  Qed.

  Lemma aggFlip_newAgg_unit q :
    new q <> []
    -> newAgg (aggFlip q) = unit.
  Proof.
    destruct q. simpl.
    destruct new0. intuition.
    intros. rewrite aggFlip_equation.
    simpl. unfold aggStep. simpl.
    assert (forall x, newAgg (aggFlip {| new := new0; newAgg := unit; oldAggs := x |}) =
  unit).
    induction new0.
    - auto.
    - specialize (IHnew0 ltac:(discriminate)).
      intros. rewrite aggFlip_equation. simpl.
      unfold aggStep. simpl. auto.
    - firstorder.
  Qed.


  Lemma aggFlip_newAgg_inv q :
    newAgg_inv q
    -> newAgg_inv (aggFlip q).
  Proof.
    unfold newAgg_inv. destruct q eqn:Eq. destruct new0.
    - auto.
    - intros. rewrite <- Eq.
      rewrite aggFlip_new_empty. simpl.
      replace (finite_op B []) with unit by auto.
      apply aggFlip_newAgg_unit. rewrite Eq. discriminate.
  Qed.

  Lemma aggFlip_oldAggs_inv news olds q :
    new_inv news q
    -> oldAggs_inv olds q
    -> oldAggs_inv (news ++ olds) (aggFlip q).
  Proof.
    revert q. revert olds.
    induction news using list_r_ind.
    - intros. simpl. destruct q.
      unfold new_inv in H. simpl in H.
      subst. auto.
    - intros. rewrite aggFlip_equation.
      destruct (new q) eqn:Enq.
      + unfold new_inv in H. rewrite rev_app_distr in H. rewrite Enq in H. simpl in H.
        discriminate.
      + specialize (IHnews (x :: olds) (aggStep q)).
        rewrite <- app_assoc. simpl. apply IHnews.
        apply aggStep_new_inv with (n := x). apply H.
        apply aggStep_oldAggs_inv with (ns := news); auto.
  Qed.

  Definition aggDequeue (q : aggQueue) : aggQueue :=
    match (oldAggs q) with
    | [] => let newQ := (aggFlip q) in
           match (oldAggs newQ) with
           | [] => newQ
           | (o :: os) => {| new := new newQ; newAgg := newAgg newQ; oldAggs := os |}
           end
   | (o :: os) => {| new := new q; newAgg := newAgg q; oldAggs := os |}
    end.

  Lemma aggDequeue_new_inv1 news q :
    oldAggs q = []
    -> new_inv news q
    -> new_inv [] (aggDequeue q).
  Proof.
    destruct q eqn:Eq. destruct oldAggs0.
    - intros.
      unfold aggDequeue. simpl. rewrite <- Eq.
      unfold new_inv. simpl. destruct (oldAggs (aggFlip q)) eqn:E.
      apply aggFlip_new_empty.
      simpl. apply aggFlip_new_empty.
    - intro. discriminate.
  Qed.

  Lemma aggDequeue_new_inv2 news q :
    oldAggs q <> []
    -> new_inv news q
    -> new_inv news (aggDequeue q).
  Proof.
    destruct q eqn:Eq. destruct oldAggs0.
    - intro. simpl in H. intuition.
    - intros. unfold aggDequeue. simpl.
      unfold new_inv in *. auto.
  Qed.

  Lemma aggDequeue_newAgg_inv q :
    newAgg_inv q -> newAgg_inv (aggDequeue q).
  Proof.
    destruct q eqn:Eq. destruct oldAggs0.
    - intros.
      unfold aggDequeue. simpl. rewrite <- Eq.
      destruct (oldAggs (aggFlip q)) eqn:E.
      + apply aggFlip_newAgg_inv. now rewrite <- Eq in H.
      + rewrite <- Eq in H. apply aggFlip_newAgg_inv in H.
        unfold newAgg_inv in *. auto.
    - auto.
  Qed.

  Lemma aggDequeue_oldAggs_inv1 n ns q :
    oldAggs q = []
    -> new_inv (n :: ns) q
    -> oldAggs_inv ns (aggDequeue q).
  Proof.
    destruct q eqn:Eq. destruct oldAggs0.
    - intros.
      unfold aggDequeue. simpl. rewrite <- Eq.
      destruct new0 eqn:E.
      + rewrite aggFlip_equation. rewrite Eq. simpl.
        unfold new_inv in H0. unfold oldAggs_inv.
        simpl in *. eapply f_equal in H0. rewrite app_length in H0.
        simpl in H0. lia.
      + rewrite <- Eq in H. rewrite <- Eq in H0.
        assert (oldAggs_inv [] q).
        { unfold oldAggs_inv. split.
          - now rewrite H.
          - rewrite H. simpl.
            intros. rewrite skipn_nil.
            destruct i; auto.
        }
        pose proof (aggFlip_oldAggs_inv _ _ _ H0 H1).
        rewrite app_nil_r in H2. destruct H2 as [H21 H22].
        destruct (oldAggs (aggFlip q)).
        * simpl in H21. lia.
        * unfold oldAggs_inv. simpl.
          split.
          ** simpl in H21. lia.
          ** intros. specialize (H22 (S i)).
             auto.
    - simpl. discriminate.
  Qed.

  Lemma aggDequeue_oldAggs_inv2 o os q :
    oldAggs q <> []
    -> oldAggs_inv (o :: os) q
    -> oldAggs_inv os (aggDequeue q).
  Proof.
    destruct q eqn:Eq. destruct oldAggs0.
    - intros. simpl in H. congruence.
    - intro. unfold oldAggs_inv.
      intros  [H1 H2].
      split.
      + simpl in *. lia.
      + simpl. simpl oldAggs in H2.
        intros. now (specialize (H2 (S i))).
  Qed.

  Lemma aggDequeue_aggQueue_inv x xs q :
    aggQueue_inv (x :: xs) q
    -> aggQueue_inv xs (aggDequeue q).
  Proof.
    intros. destruct H as [olds [news [H1 [H2 [H3 H4]]]]].
    destruct q eqn:Eq.
    rewrite <- Eq in H2 , H3, H4. rewrite <- Eq.
    unfold oldAggs_inv in H4. destruct H4 as [H4 H5].
    destruct olds eqn:Eo.
    - simpl in H1.
      exists xs , [].
        split.
      ++ now rewrite app_nil_r.
      ++ split.
         apply aggDequeue_new_inv1 with (news := news).
         destruct oldAggs0.
         * now rewrite Eq.
         * subst q. simpl in *. lia.
         * auto.
         * split.
           +++ apply aggDequeue_newAgg_inv. auto.
           +++ pose proof (aggDequeue_oldAggs_inv1 x xs q).
               assert (oldAggs q = []).
               destruct oldAggs0. now rewrite Eq.
               rewrite Eq in H4. simpl in H4. lia.
               specialize (H H0). rewrite <- H1 in H.
               now specialize (H H2).

    - exists l , news.
      split.
      + simpl in H1. now inversion H1.
      + split.
        ++ apply aggDequeue_new_inv2.
          * unfold not. intros. rewrite H in H4.
            simpl in H4. lia.
          * apply H2.
        ++ split.
           +++ apply aggDequeue_newAgg_inv. apply H3.
           +++ unfold oldAggs_inv.
               pose proof (aggDequeue_oldAggs_inv2 b l q).
               assert (oldAggs q <> []).
               destruct (oldAggs q). simpl in H4. lia.
               unfold not. discriminate.
               specialize (H H0). unfold oldAggs_inv in H.
               specialize (H ltac:(split; auto)).
               auto.
  Qed.

  Lemma aggDequeue_aggQueue_inv2 q :
    aggQueue_inv [] q
    -> aggQueue_inv [] (aggDequeue q).
  Proof.
    intros.
    assert (H' := H).
    destruct H as [olds [news [H1 [H2 [H3 H4]]]]].
    assert (olds = []).
    { destruct olds; auto. simpl in H1; discriminate. }
    subst olds. simpl in H1. subst news.
    destruct q eqn:Eq.
    rewrite <- Eq in H2 , H3, H4. rewrite <- Eq.
    unfold oldAggs_inv in H4. destruct H4 as [H4 H5].
    unfold new_inv in H2. rewrite Eq in H2. simpl in H2.
    subst new0.
    assert (oldAggs0 = []).
    { destruct oldAggs0; auto. rewrite Eq in H4. simpl in H4. lia. }
    subst oldAggs0.
    unfold newAgg_inv in H3. rewrite Eq in H3. simpl in H3.
    replace (finite_op B []) with unit in H3 by auto.
    subst newAgg0.
    rewrite Eq. unfold aggDequeue. simpl. auto.
  Qed.

  Definition aggCycle (n : B) (q : aggQueue) :=
    aggDequeue (aggEnqueue n q).

  Lemma aggCycle_aggQueue_inv x xs y q :
    aggQueue_inv (x :: xs) q
    -> aggQueue_inv (xs ++ [y]) (aggCycle y q).
  Proof.
    intros. unfold aggCycle.
    apply enqueue_aggQueue_inv with (n := y) in H.
    now apply aggDequeue_aggQueue_inv in H.
  Qed.

  Lemma aggCycle_aggQueue_inv2 y q :
    aggQueue_inv [] q
    -> aggQueue_inv [] (aggCycle y q).
  Proof.
    intros. unfold aggCycle.
    apply enqueue_aggQueue_inv with (n := y) in H. simpl in H.
    now apply aggDequeue_aggQueue_inv in H.
  Qed.

  Lemma aggCycle_aggQueue_inv3 xs x n q :
    n <= length xs
    -> aggQueue_inv (lastn n xs) q
    -> aggQueue_inv (lastn n (xs ++ [x])) (aggCycle x q).
  Proof.
    intros. destruct xs.
    - simpl in H. assert (n = 0) by lia.
      simpl. subst n. rewrite lastn_0 in *.
      now apply aggCycle_aggQueue_inv2.
    - remember (b :: xs). destruct (lastn n l) eqn:E.
      + eapply f_equal in E. rewrite lastn_length in E.
        simpl in E. assert (n = 0) by lia.
        subst n. rewrite lastn_0.
        now apply aggCycle_aggQueue_inv2.
      + apply aggCycle_aggQueue_inv with (y := x) in H0.
        enough (l0 ++ [x] = lastn n (l ++ [x])). congruence.
        destruct n eqn: En.
        * rewrite lastn_0 in E. discriminate.
        * rewrite lastn_last. pose proof (tail_lastn _ l H).
          rewrite E in H1. simpl in H1. congruence.
  Qed.


  CoFixpoint mFoldAux {A : Type} (q : aggQueue) (m : Mealy A B) :=
    {| mOut (a : A) := agg (aggCycle (mOut m a) q) ;
       mNext (a : A) := mFoldAux (aggCycle (mOut m a) q) (mNext m a)
    |}.

  Lemma mFoldAux_state {A : Type} (m : Mealy A B) (q1 : aggQueue) (l1 : list B) (l2 : nonEmpty A) :
    aggQueue_inv l1 q1
    -> exists q2, gNext (mFoldAux q1 m) l2 = mFoldAux q2 (gNext m l2)
                  /\ aggQueue_inv (lastn (length l1) (l1 ++ rev (toList (gCollect m l2)))) q2.
  Proof.
    unfold lastn. rewrite rev_app_distr. rewrite rev_involutive.
    induction l2.
    - simpl. intros.
      exists (aggCycle (mOut m a) q1).
      intuition.
      simpl.
      destruct l1 eqn:El.
      + simpl. now apply aggCycle_aggQueue_inv2.
      + apply aggCycle_aggQueue_inv with (y := mOut m a) in H.
        simpl.
        enough (l ++ [mOut m a] = (rev (firstn (length l) (rev l ++ [b])) ++ [mOut m a]))
          by congruence.
        rewrite firstn_app. rewrite rev_length. replace (length l - length l) with 0 by lia.
        simpl. rewrite app_nil_r. f_equal.
        rewrite firstn_all2.
        symmetry. apply rev_involutive.
        rewrite rev_length. lia.
    - intros. specialize (IHl2 H).
      destruct IHl2 as [q2 [IH1 IH2]].
      simpl. exists (aggCycle (mOut (gNext m l2) a) q2).
      simpl. rewrite IH1. intuition.
      destruct l1 eqn:El.
      +  simpl. now apply aggCycle_aggQueue_inv2.
      + remember (toList (gCollect m l2) ++ rev (b :: l)).
        rewrite <- El in *. destruct (length l1) eqn:El1.
        * subst l1. simpl in El1. lia.
        * simpl. replace l0 with (firstn n l0 ++ skipn n l0) in IH2 by now apply firstn_skipn.
          rewrite firstn_app in IH2. rewrite firstn_firstn in IH2.
          replace (min (S n) n) with n in IH2 by lia.
          rewrite rev_app_distr in IH2.
          rewrite firstn_length in IH2.
          assert (lt n  (length l0)).
          { rewrite Heql0. rewrite app_length.
            rewrite rev_length. lia. }
          replace (min n (length l0)) with n in IH2 by lia.
          replace (S n - n) with 1 in IH2 by lia.
          assert (length (firstn 1 (skipn n l0)) = 1).
          {
            rewrite firstn_length.
            rewrite skipn_length. subst l0.
            rewrite app_length in H0. rewrite app_length. lia.
          }
          destruct (firstn 1 (skipn n l0)).
          simpl in H1. lia.
          destruct l3; [|simpl in H1; lia].
          simpl in IH2. eapply aggCycle_aggQueue_inv.
          apply IH2.
  Qed.

  Lemma mFoldAux_result {A : Type} (m : Mealy A B) (q1 : aggQueue) (l1 : list B) (l2 : nonEmpty A) :
    aggQueue_inv l1 q1
    -> gOut (mFoldAux q1 m) l2 = finite_op _ (lastn (length l1) (l1 ++ (rev (toList (gCollect m l2))))).
  Proof.
    destruct l2.
    - intros. simpl. destruct l1.
      + simpl. eapply aggCycle_aggQueue_inv2 in H.
        apply aggQueue_agg_inv. rewrite lastn_0. apply H.
      + simpl. apply aggCycle_aggQueue_inv with (y := mOut m a) in H.
        apply aggQueue_agg_inv in H.
        replace (b :: l1 ++ [mOut m a]) with ([b] ++ (l1  ++ [mOut m a])) by auto.
        rewrite lastn_app.
        replace (S (length l1) - length (l1 ++ [mOut m a])) with 0
          by now rewrite app_length;  simpl length; lia.
        rewrite lastn_0. simpl. replace (S (length l1)) with (length (l1 ++ [mOut m a]))
          by now rewrite app_length; simpl length; lia.
        rewrite lastn_all. auto.
    - intros.  simpl.
      pose proof (mFoldAux_state m q1 l1 l2 H).
      destruct H0 as [q2 [H1 H2]].
      rewrite H1. simpl. apply aggCycle_aggQueue_inv3 with (x := mOut (gNext m l2) a) in H2.
      rewrite app_assoc. apply aggQueue_agg_inv in H2. auto.
      rewrite app_length; lia.
  Qed.

  Definition unitQueue (n : nat) :=
    {| new := [];
       newAgg := unit;
       oldAggs := repeat' unit n;
    |}.

  Lemma unitQueue_aggQueue_inv (n : nat) :
    aggQueue_inv (repeat unit n) (unitQueue n).
  Proof.
    rewrite <- repeat_repeat'. unfold aggQueue_inv.
    exists (repeat' unit n), []. split.
    - now simpl_list.
    - split.
      -- split.
      -- split.
         --- split.
         --- split.
             ---- simpl. rewrite repeat_repeat'.
                  now rewrite repeat_length.
             ---- simpl. intros. rewrite repeat_repeat'.
                  rewrite skipn_repeat. rewrite finite_op_repeat_unit.
                  now rewrite nth_repeat2.
  Qed.

  Definition mFoldWin {A : Type} (n : nat) (m : Mealy A B) :=
    mFoldAux (unitQueue n) m.

  Lemma mWinFold_result {A : Type} (m : Mealy A B) (n : nat) (l : nonEmpty A) :
    gOut (mFoldWin n m) l = finite_op _ (lastn n (rev (toList (gCollect m l)))).
  Proof.
    unfold mFoldWin.
    pose proof (unitQueue_aggQueue_inv n).
    apply mFoldAux_result with (m0 := m) (l2 := l) in H.
    rewrite H. rewrite repeat_length.
    rewrite lastn_app. rewrite <- finite_op_app. rewrite lastn_repeat.
    rewrite finite_op_repeat_unit. auto using op_unit_l.
  Qed.

End aggQueue.
