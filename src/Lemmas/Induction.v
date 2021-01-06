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
