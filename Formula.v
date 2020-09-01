From Hammer Require Import Hammer.
Require Import Lia.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import Lattice.
Require Import MTLTactics.

Import ListNotations.

Section Formula.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Inductive Formula {A : Type} : Type :=
| FAtomic : (A -> Val) -> Formula
| FDelay : nat -> Formula -> Formula
| FDelayDual : nat -> Formula -> Formula
| FAnd : Formula -> Formula -> Formula
| FOr : Formula -> Formula -> Formula
| FSometime : Formula -> Formula
| FAlways : Formula -> Formula
| FSince : Formula -> Formula -> Formula
| FSinceDual : Formula -> Formula -> Formula
| FAlwaysWithin : nat -> Formula -> Formula
| FSometimeWithin : nat -> Formula -> Formula
.

Fixpoint robustness {A : Type} (ϕ : @Formula A) (l : list A) : Val :=
  match ϕ with
  | FAtomic f => match l with
                | [] => bottom
                | (x :: xs) => f (last l x)
                 end
  | FDelay n f => match (S n) <=? length l with
                  | true => robustness f (firstn (length l - (S n)) l)
                  | false => bottom
                  end
  | FDelayDual n f => match (S n) <=? length l with
                  | true => robustness f (firstn (length l - (S n)) l)
                  | false => top
                   end
  | FAnd f g => (robustness f l) ⊓ (robustness g l)
  | FOr f g => (robustness f l) ⊔ (robustness g l)
  | FSometime f => finite_join (map (robustness f) (tl (prefixes l)))
  | FAlways f => finite_meet (map (robustness f) (tl (prefixes l)))
  | FSince f g => finite_join (map
                   (fun i =>
                      (robustness g (firstn i l))
                        ⊓ (finite_meet (map
                                          (fun j => robustness f (firstn j l))
                                          (seq (S i) (length l - i))
                                       )
                          )
                   )
                   (seq 0 (S (length l))))
  | FSinceDual f g => finite_meet (map
                   (fun i =>
                      (robustness g (firstn i l))
                        ⊔ (finite_join (map
                                          (fun j => robustness f (firstn j l))
                                          (seq (S i) (length l - i))
                                       )
                          )
                   )
                   (seq 0 (S (length l))))
  | FSometimeWithin hi f => finite_join (map (robustness f) (lastn (S hi) (tl (prefixes l))))
  | FAlwaysWithin hi f => finite_meet (map (robustness f) (lastn (S hi) (tl (prefixes l))))
  end
.


(* Note that `robustness (FDelay n ϕ) w' refers to the
 `robustness ϕ (w with (n + 1) latest elements removed)' *)
Definition FPre {A : Type} (ϕ : @Formula A) :=
  FDelay 0 ϕ.

(* `FSometimeWithin hi f' stands for `Y_[0, hi + 1] f' *)
(* `FSometimeBounded lo len` stands for `Y_[lo + 1, lo + len + 2]`*)
Definition FSometimeBounded {A : Type} (lo len : nat) (ϕ : @Formula A) :=
  FDelay lo (FSometimeWithin len ϕ).

(* `FAlwaysWithin hi f' stands for `H_[0, hi + 1] f' *)
(* `FAlwaysBounded lo len` stands for `H_[lo + 1, lo + len + 2]`*)
Definition FAlwaysBounded {A : Type} (lo len : nat) (ϕ : @Formula A) :=
  FDelayDual lo (FAlwaysWithin len ϕ).

(* Stands for Since_[0, hi + 1]*)
Definition FSinceWithin {A : Type} (hi : nat) (ϕ ψ: @Formula A) :=
  FAnd (FDelay hi ψ) (FSince ϕ ψ).

(* This represents Since_[lo+2, lo + len + 3] *)
Definition FSinceBounded {A : Type} (lo len : nat) (ϕ ψ : @Formula A) :=
  FAnd (FAlwaysWithin lo ϕ) (FDelay (S lo) (FSinceWithin len ϕ ψ)).

(* This represents Since_[lo + 1, ∞) *)
Definition FSinceAfter {A : Type} (lo : nat) (ϕ ψ : @Formula A) :=
  FDelay lo (FSince ϕ ψ).

Definition FSinceWithinDual {A : Type} (hi : nat) (ϕ ψ: @Formula A) :=
  FOr (FDelayDual hi ψ) (FSinceDual ϕ ψ).
Definition FSinceBoundedDual {A : Type} (lo len : nat) (ϕ ψ : @Formula A) :=
  FOr (FSometimeWithin lo ϕ) (FDelayDual (S lo) (FSinceWithin len ϕ ψ)).
Definition FSinceAfterDual {A : Type} (lo : nat) (ϕ ψ : @Formula A) :=
  FDelayDual lo (FSinceDual ϕ ψ).


Lemma since_inductive {A : Type} (ϕ ψ : @Formula A) (xs : list A) (x : A) :
  robustness (FSince ϕ ψ) (xs ++ [x])
   = ((robustness (FSince ϕ ψ) xs ⊓ robustness ϕ (xs ++ [x])) ⊔ robustness ψ (xs ++ [x])).
Proof.
  generalize dependent x. induction xs using list_r_ind.
  - intros. simpl. unfold finite_join. unfold finite_meet. simpl.
    repeat rewrite join_bottom_l. repeat rewrite meet_top_r.
    now rewrite meet_top_l.
  - intros. remember (xs ++ [x]) as xs0.
    replace ( robustness (FSince ϕ ψ) (xs0 ++ [x0])) with (finite_join (map
                   (fun i =>
                      (robustness ψ (firstn i (xs0 ++ [x0])))
                        ⊓ (finite_meet (map
                                          (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                                          (seq (S i) (length (xs0 ++ [x0]) - i))
                                       )
                          )
                   )
                   (seq 0 (S (length (xs0 ++ [x0]))))) ) by reflexivity.
    rewrite app_length. simpl length.
    rewrite map_seq_last. replace (length xs0 + 1) with (S (length xs0)) at 1 by lia.
    assert (S1 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a (xs0 ++ [x0]))
  ⊓ finite_meet
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a)))) =
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet
  (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a))))).
    intros. rewrite in_seq in H. rewrite firstn_app. replace (a - length xs0) with 0 by lia.
    simpl firstn. now rewrite app_nil_r.
    rewrite map_ext_in with
        (f :=
           (fun i : nat =>
              robustness ψ (firstn i (xs0 ++ [x0]))
                         ⊓ finite_meet
                         (map (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                              (seq (S i) (length xs0 + 1 - i)))
           )
        )
        (g :=
           (fun i : nat =>
              robustness ψ (firstn i xs0)
                         ⊓ finite_meet

                         (map (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                              (seq (S i) (length xs0 + 1 - i)))
           )
        ) by exact S1.
    clear S1.
    replace (length xs0 + 1 - (0 + (length xs0 + 1))) with 0 by lia.
    simpl seq at 3. simpl map at 3.
    replace (finite_meet []) with top by auto. rewrite meet_top_r.
    replace (0 + (length xs0 + 1)) with (length xs0 + length [x0]) by auto.
    rewrite <- app_length. rewrite firstn_all. rewrite finite_join_app.
    assert (finite_join [robustness ψ (xs0 ++ [x0])] = robustness ψ (xs0 ++ [x0])).
    unfold finite_join. simpl. now rewrite join_bottom_l.
    rewrite H. clear H.
    assert (S2 :forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a)))) =
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet
  (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (S (length xs0 - a)))))).
    intros. rewrite in_seq in H. simpl in H. f_equal. f_equal. f_equal. f_equal. lia.
    rewrite map_ext_in with (f := 
        (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (length xs0 + 1 - i)))))
        (g :=
        (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (S (length xs0 - i)))))) by exact S2.
    clear S2.
    assert ( S3 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (S (length xs0 - a))))) =
 (robustness ψ (firstn a xs0)
   ⊓ finite_meet
       (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 - a)))
     ⊓ robustness ϕ (xs0 ++ [x0]))).
    intros. rewrite in_seq in H. rewrite map_seq_last.
    replace (S a + (length xs0 - a)) with ((length xs0) + 1) by lia.
    replace (length xs0 + 1) with (length xs0 + length [x0]) by auto.
    rewrite <- app_length. rewrite firstn_all. rewrite finite_meet_app.
    unfold finite_meet at 2. simpl fold_left. now rewrite meet_top_l.

    rewrite map_ext_in with
        (f := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (S (length xs0 - i))))))
        (g := (fun i : nat =>
         (robustness ψ (firstn i xs0)
   ⊓ finite_meet
       (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S i) (length xs0 - i)))
     ⊓ robustness ϕ (xs0 ++ [x0])))) by exact S3.
    clear S3.
    assert (S4 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 - a)))
    ⊓ robustness ϕ (xs0 ++ [x0])) =
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a)))
  ⊓ robustness ϕ (xs0 ++ [x0]))).
    { intros. rewrite in_seq in H.
      f_equal. f_equal. f_equal.
      assert (SS4 : forall a0 : nat,
 In a0 (seq (S a) (length xs0 - a)) ->
 robustness ϕ (firstn a0 (xs0 ++ [x0])) = robustness ϕ (firstn a0 xs0)
             ).
      intros. rewrite in_seq in H0.
      rewrite firstn_app. replace (a0 - length xs0) with 0 by lia.
      simpl firstn. now rewrite app_nil_r.
      now rewrite map_ext_in with
          (f := (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))))
          (g := (fun j : nat => robustness ϕ (firstn j (xs0)))) by exact SS4.
    }
    rewrite map_ext_in with
        (f := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S i) (length xs0 - i)))
             ⊓ robustness ϕ (xs0 ++ [x0])))
        (g := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet
             (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))
             ⊓ robustness ϕ (xs0 ++ [x0]))) by exact S4.
    clear S4.
    assert (S5 : forall a : nat,
 (robustness ψ (firstn a xs0)
  ⊓ finite_meet (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a)))
    ⊓ robustness ϕ (xs0 ++ [x0])) =
 (robustness ϕ (xs0 ++ [x0])
  ⊓ robustness ψ (firstn a xs0)
  ⊓ finite_meet (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a))))).
    intros. rewrite meet_comm. rewrite meet_assoc. rewrite meet_comm. now rewrite meet_assoc.
    rewrite map_ext with
        (f := ( fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊓ finite_meet (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))
           ⊓ robustness ϕ (xs0 ++ [x0])))
        (g := (fun i : nat =>
                 robustness ϕ (xs0 ++ [x0]) ⊓
         (fun i => robustness ψ (firstn i xs0)
         ⊓ finite_meet (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))) i
              )
        )
      by exact S5.
    clear S5.
    replace (S (length xs0)) with (length xs0 + 1) by lia.
    replace (seq 0 (length xs0 + 1)) with ((seq 0 (length xs0)) ++ (seq (length xs0) 1)) by now rewrite seq_app. simpl seq.
    rewrite finite_meet_distr.
    replace (seq 0 (length xs0) ++ [length xs0]) with (seq 0 (length xs0) ++ seq (length xs0) 1) by auto.
    replace ((seq 0 (length xs0)) ++ (seq (length xs0) 1)) with (seq 0 (length xs0 + 1)) by now rewrite seq_app.
    replace (length xs0 + 1) with (S (length xs0)) by lia.
    replace (finite_join
        (map
           (fun i : nat =>
            robustness ψ (firstn i xs0)
            ⊓ finite_meet
                (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i))))
           (seq 0 (S (length xs0)))))
      with
        (robustness (FSince ϕ ψ) xs0) by auto.
    now rewrite meet_comm.
Qed.

Lemma sinceDual_inductive {A : Type} (ϕ ψ : @Formula A) (xs : list A) (x : A) :
  robustness (FSinceDual ϕ ψ) (xs ++ [x])
   = ((robustness (FSinceDual ϕ ψ) xs ⊔ robustness ϕ (xs ++ [x])) ⊓ robustness ψ (xs ++ [x])).
Proof.
  generalize dependent x. induction xs using list_r_ind.
  - intros. simpl. unfold finite_meet. unfold finite_join. simpl.
    repeat rewrite meet_top_l. repeat rewrite join_bottom_r.
    now rewrite join_bottom_l.
  - intros. remember (xs ++ [x]) as xs0.
    replace ( robustness (FSinceDual ϕ ψ) (xs0 ++ [x0])) with (finite_meet (map
                   (fun i =>
                      (robustness ψ (firstn i (xs0 ++ [x0])))
                        ⊔ (finite_join (map
                                          (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                                          (seq (S i) (length (xs0 ++ [x0]) - i))
                                       )
                          )
                   )
                   (seq 0 (S (length (xs0 ++ [x0]))))) ) by reflexivity.
    rewrite app_length. simpl length.
    rewrite map_seq_last. replace (length xs0 + 1) with (S (length xs0)) at 1 by lia.
    assert (S1 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a (xs0 ++ [x0]))
  ⊔ finite_join
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a)))) =
 (robustness ψ (firstn a xs0)
  ⊔ finite_join
  (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a))))).
    intros. rewrite in_seq in H. rewrite firstn_app. replace (a - length xs0) with 0 by lia.
    simpl firstn. now rewrite app_nil_r.
    rewrite map_ext_in with
        (f :=
           (fun i : nat =>
              robustness ψ (firstn i (xs0 ++ [x0]))
                         ⊔ finite_join
                         (map (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                              (seq (S i) (length xs0 + 1 - i)))
           )
        )
        (g :=
           (fun i : nat =>
              robustness ψ (firstn i xs0)
                         ⊔ finite_join

                         (map (fun j => robustness ϕ (firstn j (xs0 ++ [x0])))
                              (seq (S i) (length xs0 + 1 - i)))
           )
        ) by exact S1.
    clear S1.
    replace (length xs0 + 1 - (0 + (length xs0 + 1))) with 0 by lia.
    simpl seq at 3. simpl map at 3.
    replace (finite_join []) with bottom by auto. rewrite join_bottom_r.
    replace (0 + (length xs0 + 1)) with (length xs0 + length [x0]) by auto.
    rewrite <- app_length. rewrite firstn_all. rewrite finite_meet_app.
    assert (finite_meet [robustness ψ (xs0 ++ [x0])] = robustness ψ (xs0 ++ [x0])).
    unfold finite_meet. simpl. now rewrite meet_top_l.
    rewrite H. clear H.
    assert (S2 :forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊔ finite_join
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 + 1 - a)))) =
 (robustness ψ (firstn a xs0)
  ⊔ finite_join
  (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (S (length xs0 - a)))))).
    intros. rewrite in_seq in H. simpl in H. f_equal. f_equal. f_equal. f_equal. lia.
    rewrite map_ext_in with (f := 
        (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (length xs0 + 1 - i)))))
        (g :=
        (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (S (length xs0 - i)))))) by exact S2.
    clear S2.
    assert ( S3 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊔ finite_join
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (S (length xs0 - a))))) =
 (robustness ψ (firstn a xs0)
   ⊔ finite_join
       (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 - a)))
     ⊔ robustness ϕ (xs0 ++ [x0]))).
    intros. rewrite in_seq in H. rewrite map_seq_last.
    replace (S a + (length xs0 - a)) with ((length xs0) + 1) by lia.
    replace (length xs0 + 1) with (length xs0 + length [x0]) by auto.
    rewrite <- app_length. rewrite firstn_all. rewrite finite_join_app.
    unfold finite_join at 2. simpl fold_left. now rewrite join_bottom_l.
    rewrite map_ext_in with
        (f := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0])))
                  (seq (S i) (S (length xs0 - i))))))
        (g := (fun i : nat =>
         (robustness ψ (firstn i xs0)
   ⊔ finite_join
       (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S i) (length xs0 - i)))
     ⊔ robustness ϕ (xs0 ++ [x0])))) by exact S3.
    clear S3.
    assert (S4 : forall a : nat,
 In a (seq 0 (S (length xs0))) ->
 (robustness ψ (firstn a xs0)
  ⊔ finite_join
      (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S a) (length xs0 - a)))
    ⊔ robustness ϕ (xs0 ++ [x0])) =
 (robustness ψ (firstn a xs0)
  ⊔ finite_join (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a)))
  ⊔ robustness ϕ (xs0 ++ [x0]))).
    { intros. rewrite in_seq in H.
      f_equal. f_equal. f_equal.
      assert (SS4 : forall a0 : nat,
 In a0 (seq (S a) (length xs0 - a)) ->
 robustness ϕ (firstn a0 (xs0 ++ [x0])) = robustness ϕ (firstn a0 xs0)
             ).
      intros. rewrite in_seq in H0.
      rewrite firstn_app. replace (a0 - length xs0) with 0 by lia.
      simpl firstn. now rewrite app_nil_r.
      now rewrite map_ext_in with
          (f := (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))))
          (g := (fun j : nat => robustness ϕ (firstn j (xs0)))) by exact SS4.
    }
    rewrite map_ext_in with
        (f := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join
             (map (fun j : nat => robustness ϕ (firstn j (xs0 ++ [x0]))) (seq (S i) (length xs0 - i)))
             ⊔ robustness ϕ (xs0 ++ [x0])))
        (g := (fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join
             (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))
             ⊔ robustness ϕ (xs0 ++ [x0]))) by exact S4.
    clear S4.
    assert (S5 : forall a : nat,
 (robustness ψ (firstn a xs0)
  ⊔ finite_join (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a)))
    ⊔ robustness ϕ (xs0 ++ [x0])) =
 (robustness ϕ (xs0 ++ [x0])
  ⊔ robustness ψ (firstn a xs0)
  ⊔ finite_join (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S a) (length xs0 - a))))).
    intros. rewrite join_comm. rewrite join_assoc. rewrite join_comm. now rewrite join_assoc.
    rewrite map_ext with
        (f := ( fun i : nat =>
         robustness ψ (firstn i xs0)
         ⊔ finite_join (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))
           ⊔ robustness ϕ (xs0 ++ [x0])))
        (g := (fun i : nat =>
                 robustness ϕ (xs0 ++ [x0]) ⊔
         (fun i => robustness ψ (firstn i xs0)
         ⊔ finite_join (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i)))) i
              )
        )
      by exact S5.
    clear S5.
    replace (S (length xs0)) with (length xs0 + 1) by lia.
    replace (seq 0 (length xs0 + 1)) with ((seq 0 (length xs0)) ++ (seq (length xs0) 1)) by now rewrite seq_app. simpl seq.
    rewrite finite_join_distr.
    replace (seq 0 (length xs0) ++ [length xs0]) with (seq 0 (length xs0) ++ seq (length xs0) 1) by auto.
    replace ((seq 0 (length xs0)) ++ (seq (length xs0) 1)) with (seq 0 (length xs0 + 1)) by now rewrite seq_app.
    replace (length xs0 + 1) with (S (length xs0)) by lia.
    replace (finite_meet
        (map
           (fun i : nat =>
            robustness ψ (firstn i xs0)
            ⊔ finite_join
                (map (fun j : nat => robustness ϕ (firstn j xs0)) (seq (S i) (length xs0 - i))))
           (seq 0 (S (length xs0)))))
      with
        (robustness (FSinceDual ϕ ψ) xs0) by auto.
    now rewrite join_comm.
Qed.
End Formula.
