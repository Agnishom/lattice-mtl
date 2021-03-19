(**

This file contains the proof that the normalization procedure from [../Syntax/Normal.v] also semantically makes sense.
This makes use of all the other proofs in this directory, including [Equivalences.v], [SimpleProperties.v], [LemmaThirteen.v].

*)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.
From Syntax Require Import Normal.

Require Import InfRobustness.
Require Import SimpleProperties.
Require Import Equivalences.
Require Import Incremental.
Require Import LemmaThirteen.

Section NormalizeCorrect.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.


Lemma normalize_correctness :
  forall (ϕ : Formula A) τ i,
    infRobustness ϕ τ i = infRobustness (normalize ϕ) τ i.
Proof.
  induction ϕ; intros.
  - auto.
  - simpl. congruence.
  - simpl. congruence.
  - simpl normalize. destruct n eqn:En.
    + simpl. unfold join_b.
      under op_b_ext_in => j.
      rewrite IHϕ. over. auto.
    + destruct (S n1 =? n0) eqn:En0.
      * simpl. unfold join_b.
        under op_b_ext_in => j.
        rewrite IHϕ. over. auto.
      * destruct (S n1 <? n0) eqn:En1.
        -- rewrite -> Nat.ltb_lt in En1.
           rewrite sometime_delay_bounded. lia.
           simpl. unfold join_b at 1.
           under op_b_ext_in => j. intros.
           unfold join_b at 1. under op_b_ext_in => k. rewrite IHϕ.
           over. over. auto.
        -- rewrite -> Nat.ltb_ge in En1.
           rewrite -> Nat.eqb_neq in En0.
           rewrite fSometime_hi_lo. lia. auto.
   - simpl normalize. destruct n eqn:En.
    + simpl. unfold meet_b.
      under op_b_ext_in => j.
      rewrite IHϕ. over. auto.
    + destruct (S n1 =? n0) eqn:En0.
      * simpl. unfold meet_b.
        under op_b_ext_in => j.
        rewrite IHϕ. over. auto.
      * destruct (S n1 <? n0) eqn:En1.
        -- rewrite -> Nat.ltb_lt in En1.
           rewrite always_delay_bounded. lia.
           simpl. unfold meet_b at 1.
           under op_b_ext_in => j. intros.
           unfold meet_b at 1. under op_b_ext_in => k. rewrite IHϕ.
           over. over. auto.
        -- rewrite -> Nat.ltb_ge in En1.
           rewrite -> Nat.eqb_neq in En0.
           rewrite fAlways_hi_lo. lia. auto.
   - destruct n.
     + simpl normalize.
       simpl. unfold join_b.
       under op_b_ext_in => j. rewrite IHϕ. over.
       auto.
     + simpl normalize.
       rewrite sometime_delay_unbounded.
       repeat rewrite fdelay_correctness.
       destruct (S n <=? i).
       simpl. unfold join_b.
       under op_b_ext_in => j.
       rewrite IHϕ. over. auto. auto.
   - destruct n.
     + simpl normalize.
       simpl. unfold meet_b.
       under op_b_ext_in => j. rewrite IHϕ. over.
       auto.
     + simpl normalize.
       rewrite always_delay_unbounded.
       repeat rewrite fdelayDual_correctness.
       destruct (S n <=? i).
       simpl. unfold meet_b.
       under op_b_ext_in => j.
       rewrite IHϕ. over. auto. auto.
   - simpl normalize. destruct n.
     + rewrite since_sometime_bounded.
       simpl.
       unfold join_b at 1.
       under join_b_ext_in => j. rewrite IHϕ2. over.
       unfold meet_i at 1.
       under op_b_ext_in => j. rewrite IHϕ2.
       under op_i_ext_in => k. rewrite IHϕ1. over.
       over. auto.
     + destruct (n <? n0) eqn:En.
       * rewrite -> Nat.ltb_lt in En.
         rewrite since_always_bounded.
         assumption.
         remember (FDelay _ _) as f. remember (FAlways _ _ _) as g.
         simpl infRobustness at 1.
         remember (FDelay (S n) (FAnd _ _)) as f'.
         remember (FAlways 0 n (normalize _)) as g'.
         simpl infRobustness at 3. rewrite Heqg. rewrite Heqg'.
         f_equal.
         -- subst. repeat rewrite fdelay_correctness.
            destruct (S n <=? i).
            ** rewrite since_sometime_bounded.
               simpl. under join_b_ext_in => j.
               rewrite IHϕ2. under meet_i_ext_in => k.
               rewrite IHϕ1. over. over.
               f_equal. under join_b_ext_in => j.
               rewrite IHϕ2. over. auto.
            ** auto.
         -- simpl. under meet_b_ext_in => j.
            rewrite IHϕ1. over. auto.
       * rewrite -> Nat.ltb_ge in En.
         rewrite -> fSince_hi_lo by lia.
         auto.
   - simpl normalize. destruct n.
     + rewrite sinceDual_always_bounded.
       simpl.
       unfold meet_b at 1.
       under meet_b_ext_in => j. rewrite IHϕ2. over.
       unfold join_i at 1.
       under op_b_ext_in => j. rewrite IHϕ2.
       under op_i_ext_in => k. rewrite IHϕ1. over.
       over. auto.
     + destruct (n <? n0) eqn:En.
       * rewrite -> Nat.ltb_lt in En.
         rewrite sinceDual_sometime_bounded.
         assumption.
         remember (FDelayDual _ _) as f. remember (FSometime _ _ _) as g.
         simpl infRobustness at 1.
         remember (FDelayDual (S n) (FOr _ _)) as f'.
         remember (FSometime 0 n (normalize _)) as g'.
         simpl infRobustness at 3. rewrite Heqg. rewrite Heqg'.
         f_equal.
         -- subst. repeat rewrite fdelayDual_correctness.
            destruct (S n <=? i).
            ** rewrite sinceDual_always_bounded.
               simpl. under meet_b_ext_in => j.
               rewrite IHϕ2. under join_i_ext_in => k.
               rewrite IHϕ1. over. over.
               f_equal. under meet_b_ext_in => j.
               rewrite IHϕ2. over. auto.
            ** auto.
         -- simpl. under join_b_ext_in => j.
            rewrite IHϕ1. over. auto.
       * rewrite -> Nat.ltb_ge in En.
         rewrite -> fSinceDual_hi_lo by lia.
         auto.
   - simpl normalize. destruct n.
     + simpl. under join_b_ext_in => j.
       rewrite IHϕ2. under meet_i_ext_in => k.
       rewrite IHϕ1. over. over.
       auto.
     + rewrite since_always_unbounded.
       remember (FDelay _ _) as f. remember (FAlways _ _ _) as g.
       simpl infRobustness at 1.
       remember (FDelay (S n) (FSinceUnbounded 0 (normalize ϕ1) _)) as f'.
       remember (FAlways 0 n (normalize _)) as g'.
       simpl infRobustness at 3. rewrite Heqg. rewrite Heqg'.
       f_equal.
       * subst. repeat rewrite fdelay_correctness.
         destruct (S n <=? i).
         ++ simpl. under join_b_ext_in => j.
            rewrite IHϕ2. under meet_i_ext_in => k.
            rewrite IHϕ1. over. over. auto.
         ++ auto.
       * simpl. under meet_b_ext_in => j. rewrite IHϕ1. over.
         auto.
   - simpl normalize. destruct n.
     + simpl. under meet_b_ext_in => j.
       rewrite IHϕ2. under join_i_ext_in => k.
       rewrite IHϕ1. over. over.
       auto.
     + rewrite sinceDual_sometime_unbounded.
       remember (FDelayDual _ _) as f. remember (FSometime _ _ _) as g.
       simpl infRobustness at 1.
       remember (FDelayDual (S n) (FSinceDualUnbounded 0 (normalize ϕ1) _)) as f'.
       remember (FSometime 0 n (normalize _)) as g'.
       simpl infRobustness at 3. rewrite Heqg. rewrite Heqg'.
       f_equal.
       * subst. repeat rewrite fdelayDual_correctness.
         destruct (S n <=? i).
         ++ simpl. under meet_b_ext_in => j.
            rewrite IHϕ2. under join_i_ext_in => k.
            rewrite IHϕ1. over. over. auto.
         ++ auto.
       * simpl. under join_b_ext_in => j. rewrite IHϕ1. over.
         auto.
Qed.


End NormalizeCorrect.
