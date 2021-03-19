(**

This file contains:

1. The definition of a queue using two lists.
2. A Mealy machine that uses a queue by repeatedly enqueing and dequeing with the effect of producing a lag in the stream.

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

Require Import Mealy.

Section mQueue.

  Variable A B : Type.
  Variable init : B.

  (* Definitions: [Queue], [enqueue], [dequeue], [queueHead] *)

  Record Queue : Type :=
    {front : list B; back : list B}.

  Definition enqueue (new : B) (q : Queue) : Queue :=
    Build_Queue (front q) (new :: back q).

  Definition dequeue (q : Queue) : Queue :=
    match (front q) with
    | (x :: xs) => Build_Queue xs (back q)
    | [] => match (rev' (back q)) with
           | [] => Build_Queue [] []
           | (y :: ys) => Build_Queue ys []
           end
    end.

  Definition queueHead (q : Queue) : option B :=
    match (front q) with
    | (x :: xs) => Some x
    | [] => match (rev' (back q)) with
            | (y :: ys) => Some y
            | [] => None
            end
    end.

  (* Claims about the contents of the queue and how they behave with respect to the operations *)

  Definition queueContents (q : Queue): list B :=
    back q ++ rev (front q).

  Lemma length_enequeue new q :
    length  (queueContents (enqueue new q))  = S (length (queueContents q)).
  Proof.
    auto.
  Qed.

  Lemma queueHead_queueContents (q : Queue) :
    queueHead q = head (rev (queueContents q)).
  Proof.
    unfold queueContents; unfold queueHead.
    unfold rev'. rewrite <- rev_alt.
    destruct q. simpl. destruct front0 eqn:E; destruct back0 eqn:F; auto.
    - simpl. simpl_list. auto.
    - simpl. simpl_list. auto.
    - simpl. simpl_list. repeat rewrite rev_app_distr. rewrite rev_involutive.
      simpl. auto.
  Qed.

  Lemma length_dequeue q :
    length  (queueContents (dequeue q))  = pred (length (queueContents q)).
  Proof.
    destruct q; destruct front0; destruct back0; simpl; simpl_list; auto.
    - unfold dequeue.
      unfold rev'. rewrite <- rev_alt.
      simpl. destruct (rev back0 ++ [b]) eqn:E.
      + symmetry in E. apply app_cons_not_nil in E. intuition.
      + unfold queueContents. simpl. rewrite rev_length.
        eapply f_equal in E. rewrite app_length in E.
        simpl in E. rewrite rev_length in E.
        lia.
    - unfold dequeue. simpl. unfold queueContents.
      simpl. simpl_list. simpl. lia.
    - simpl. lia.
  Qed.

  (* An enqueue, followed by a dequeue.
     This definition is useful to us since this is how the monitor produces a fixed lag.  *)

  Definition cycle (new : B) (q : Queue) : Queue :=
    dequeue (enqueue new q).

  Lemma length_cycle new q :
    length (queueContents (cycle new q)) = length (queueContents q).
  Proof.
    unfold cycle.
    rewrite length_dequeue. rewrite length_enequeue.
    lia.
  Qed.

  Lemma queueContents_enqueue new q :
    (queueContents (enqueue new q)) = new :: (queueContents q).
  Proof.
    auto.
  Qed.

  (** This Mealy machine starts with a queue which contains all units in the beginning,
      and then it repeats the [cycle] operation with every new element from the trace *)

  CoFixpoint delayWith (q : Queue) (m : Mealy A B) : Mealy A B :=
  {|
    mOut (a : A) :=
      match (queueHead q) with
      | Some x => x
      | None => mOut m a
      end;
    mNext (a : A) :=
      delayWith (cycle (mOut m a) q) (mNext m a);
  |}.

  Definition delay (n : nat) (m : Mealy A B) :=
    delayWith (Build_Queue (repeat' init n) []) m.

  (* These are the invariants we can claim about the machine described above *)

  Lemma delayWith_state (q : Queue) (m : Mealy A B) (l : nonEmpty A) :
    forall initSeg, initSeg = (back q) ++ rev (front q)
 -> forall k, k = length initSeg
 -> forall stream, stream = (toList (gCollect m l)) ++ initSeg
 -> forall lastSeg, lastSeg = firstn k stream
 -> exists newFront newBack,
                lastSeg = newBack ++ rev newFront
              /\ length lastSeg = k
              /\ gNext (delayWith q m) l = delayWith (Build_Queue newFront newBack) (gNext m l).
  Proof.
    revert q m.
    induction l.
    - intros. simpl in *.
      exists (front (cycle (mOut m a) q)).
      exists (back (cycle (mOut m a) q)).
      destruct q eqn:Eq; simpl in *.
      destruct front0; simpl in *.
      + split.
        { subst. simpl_list. unfold cycle. unfold enqueue. simpl.
          unfold dequeue.
          unfold rev'. rewrite <- rev_alt.
          simpl. destruct (rev back0) eqn:Eback.
          - eapply f_equal in Eback. rewrite rev_involutive in Eback. simpl in Eback.
            subst. auto.
          - simpl. rewrite rev_app_distr. simpl.
            eapply f_equal in Eback. rewrite rev_involutive in Eback. simpl in Eback.
            subst.  simpl_list. simpl.
            replace (length l + 1) with (S (length l)) by lia.
            simpl. f_equal. rewrite firstn_app.
            simpl_list. rewrite <- rev_length at 1. rewrite firstn_all.
            replace (_ - _) with 0 by lia. simpl. simpl_list. auto.
        }
        { split.
          { subst. simpl_list. rewrite firstn_length. simpl. lia. }
          { f_equal.
            remember (cycle (mOut m a) {| front := []; back := back0 |}).
            destruct q0. auto. }
        }
      + split.
        { subst. simpl_list. simpl.
          replace (mOut m a :: (back0 ++ rev front0 ++ [b]))
            with ((mOut m a :: (back0 ++ rev front0)) ++ [b]).
          rewrite firstn_app. simpl. rewrite firstn_all2.
          rewrite app_length. rewrite rev_length.
          replace (_ + _ - _) with 0 by lia. simpl. simpl_list. auto.
          { simpl. rewrite app_length. rewrite rev_length. lia. }
          { simpl. rewrite app_assoc. auto. }
        }
        { split.
          { subst. rewrite firstn_length. simpl. repeat rewrite app_length.
            lia. }
          { f_equal.
          }
        }
    - intros.
      specialize (IHl q m initSeg H k H0).
      pose (stream' := toList (gCollect m l) ++ initSeg).
      specialize (IHl stream' eq_refl).
      pose (lastSeg' := firstn k stream').
      specialize (IHl lastSeg' eq_refl).
      destruct IHl as [oldFront [oldBack IHl]].
      destruct IHl as [IH1 [IH2 IH3]].
      exists (front (cycle (mOut (gNext m l) a) (Build_Queue oldFront oldBack) )).
      exists (back (cycle (mOut (gNext m l) a) (Build_Queue oldFront oldBack) )).
      simpl in *.
      fold stream' in H1. rewrite H1 in H2.
      destruct k.
      + simpl in H2. subst.
        eapply f_equal in IH1. rewrite app_length in IH1.
        rewrite IH2 in IH1.
        assert (length oldBack = 0) by lia.
        assert (length (rev oldFront) = 0) by lia.
        assert (oldBack = []) by now destruct oldBack; subst; simpl in H; [auto | lia].
        rewrite rev_length in H1.
        assert (oldFront = []) by now destruct oldFront; subst; simpl in H1; [auto | lia].
        simpl in *. subst. simpl in *.
        intuition. rewrite IH3. auto.
      + simpl in H2. split.
        {
          destruct oldFront eqn:Efront.
          - destruct oldBack eqn:Eback.
            + simpl in IH1. subst. rewrite IH1 in IH2. simpl in IH2. lia.
            + simpl in IH1. rewrite app_nil_r in IH1.
              unfold cycle. unfold enqueue.
              simpl. unfold dequeue.
              unfold rev'. rewrite <- rev_alt.
              simpl.
              destruct ( (rev l0 ++ [b]) ++ [mOut (gNext m l) a] ) eqn:EE.
              * eapply f_equal in EE. rewrite app_length in EE. simpl in EE. lia.
              * simpl. subst. eapply f_equal in EE.
                rewrite rev_app_distr in EE. simpl in EE.
                rewrite rev_app_distr in EE. simpl in EE.
                rewrite rev_involutive in EE. rewrite <- IH1 in EE.
                unfold lastSeg' in EE.
                assert (lt k (length stream')) by
                    now unfold lastSeg' in IH2; rewrite firstn_length in IH2; lia.
                replace stream' with (firstn k stream' ++ skipn k stream') in EE
                  by auto using firstn_skipn.
                rewrite firstn_app in EE. rewrite firstn_firstn in EE.
                replace (min (S k) k) with k in EE by lia.
                rewrite firstn_length in EE.
                replace (min k (length stream')) with k in EE by lia.
                replace (S k - k) with 1 in EE by lia.
                simpl in EE. destruct (skipn k stream') eqn:ES.
                ** pose proof (firstn_skipn k stream').
                   eapply f_equal in H1. rewrite app_length in H1.
                   rewrite firstn_length in H1.
                   assert (length (skipn k stream') = 0) by now rewrite ES.
                   lia.
                ** replace ( mOut (gNext m l) a :: firstn k stream' ++ [b1] )
                     with ( (mOut (gNext m l) a :: firstn k stream') ++ [b1] ) in EE by auto.
                   eapply f_equal in EE. rewrite rev_app_distr in EE.
                   rewrite rev_app_distr in EE. simpl in EE.
                   inversion EE. rewrite rev_involutive in H3.
                   eapply f_equal in H3. rewrite rev_app_distr in H3.
                   rewrite rev_involutive in H3. simpl in H3. apply H3.
          - simpl. rewrite H2. f_equal. unfold lastSeg' in IH1.
            assert (lt k  (length stream')) by
                now unfold lastSeg' in IH2; rewrite firstn_length in IH2; lia.
            replace stream' with (firstn k stream' ++ skipn k stream') in IH1
              by auto using firstn_skipn.
            rewrite firstn_app in IH1. rewrite firstn_firstn in IH1.
            replace (min (S k) k) with k in IH1 by lia.
            rewrite firstn_length in IH1.
            replace (min k (length stream')) with k in IH1 by lia.
            replace (S k - k) with 1 in IH1 by lia.
            simpl in IH1. destruct (skipn k stream') eqn:ES.
            ** pose proof (firstn_skipn k stream').
               eapply f_equal in H4. rewrite app_length in H4.
               rewrite firstn_length in H4.
               rewrite ES in H4. simpl in H4. lia.
            ** rewrite app_assoc in IH1.
               eapply f_equal in IH1. rewrite rev_app_distr in IH1.
               rewrite rev_app_distr in IH1. simpl in IH1.
               inversion IH1. eapply f_equal in H6. now repeat rewrite rev_involutive in H6.
        }
        split.
        { subst lastSeg. simpl. f_equal.
          apply firstn_length_le.
          unfold lastSeg' in IH2.
          rewrite firstn_length in IH2. lia.
        }
        { rewrite IH3; simpl.
          remember (cycle (mOut (gNext m l) a) {| front := oldFront; back := oldBack |}).
          destruct q0. auto.
        }
  Qed.

  (* This is the claim we are interested in. It shows that the combinator [delay n] indeed produces the nth last element in the stream *)

  Lemma delay_result (n : nat) (m : Mealy A B) (l : nonEmpty A) :
    gOut (delay n m) l
    = nth n (toList (gCollect m l)) init.
  Proof.
    destruct l.
    - destruct n eqn:En.
      + auto.
      + simpl. rewrite repeat_repeat'. destruct n0; auto.
    - unfold delay. simpl gOut.
    remember ({| front := repeat init n; back := [] |}).
    pose (initSeg := (back q) ++ rev (front q)).
    pose (k := length initSeg).
    pose (stream := (toList (gCollect m l) ++ initSeg)).
    pose (lastSeg := firstn k stream).
    specialize (delayWith_state q m l initSeg eq_refl k eq_refl stream eq_refl lastSeg eq_refl).
    rewrite <- repeat_repeat' in Heqq.
    intros [newFront [newBack [H1 [H2 H3]]]].
    assert (k = n).
    { unfold k. unfold initSeg. rewrite Heqq.
      simpl. rewrite rev_length. rewrite repeat_repeat'. rewrite repeat_length. auto. }
    subst k. rewrite <- Heqq. rewrite H3.
    simpl mOut. simpl gCollect.
    rewrite queueHead_queueContents. unfold queueContents.
    simpl front. simpl back.
    rewrite <- H1. unfold lastSeg. rewrite H.
    destruct n; [auto | ].
    simpl toList. unfold stream. unfold initSeg. rewrite Heqq.
    simpl back. simpl front. rewrite app_nil_l.
    rewrite repeat_repeat'.
    simpl rev at 2. rewrite <- repeat_rev. rewrite repeat_snoc_cons.
    replace (init :: repeat init n) with (repeat init (S n)) by auto.
    rewrite firstn_app. rewrite rev_app_distr.
    rewrite firstn_repeat. rewrite <- repeat_rev.
    replace (min (S n - _) (S n)) with (S n - length (toList (gCollect m l))) by lia.
    destruct (Compare_dec.le_lt_dec (S n) (length (toList (gCollect m l)))).
      + replace (S n - length (toList (gCollect m l))) with 0 by lia.
        simpl repeat. rewrite app_nil_l.
        simpl nth. rewrite nth_hd_error with (d := init).
        auto. lia.
      + replace (_ - _) with (S (n - length (toList (gCollect m l)))) by lia.
        simpl repeat. simpl hd_error. simpl.
        now rewrite nth_overflow by lia.
  Qed.

End mQueue.

Arguments delay {A B}.
