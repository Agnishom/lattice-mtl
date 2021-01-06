Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.

Require Import Induction.

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
