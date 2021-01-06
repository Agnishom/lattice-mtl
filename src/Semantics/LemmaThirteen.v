Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.

Require Import InfRobustness.
Require Import SimpleProperties.
Require Import Equivalences.
Require Import Incremental.

Section LemmaThirteen.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.


Lemma since_sometime_bounded :
  forall (ϕ ψ : Formula A) τ a i,
    infRobustness (FSince 0 a ϕ ψ) τ i
    = infRobustness (FAnd (FSinceUnbounded 0 ϕ ψ) (FSometime 0 a ψ)) τ i.
Proof.
  intros. simpl.
  remember (min i a) as K.
  pose (t := fun j => infRobustness ψ τ (i - j)).
  pose (s := fun j => infRobustness ϕ τ (i - j)).
  fold s. fold t. under join_b_ext => j.
  replace (infRobustness _ _ _) with (t j) by auto.
  over. under [in RHS]join_b_ext => j.
  replace (infRobustness _ _ _) with (t j) by auto.
  over.
  remember (join_b 0 K (fun j : nat => t j ⊓ meet_i 0 j s)) as L.
  remember (join_b 0 K t) as Q.
  remember (join_b 0 i (fun j : nat => t j ⊓ meet_i 0 j s)) as R.
  destruct (Compare_dec.dec_le i a).
  { replace (min i a) with i in HeqK by lia. subst K.
    rewrite <- HeqL in HeqR. subst R. apply lattice_le_antisym.
    apply meet_inf. reflexivity.
    subst L Q. apply join_b_preserves_le. intros.
    apply meet_ge.
    apply meet_ge.
  }
  { unfold join_b in HeqR. rewrite -> op_b_app with (hi1 := K) in HeqR by lia.
    fold join_b in HeqR. rewrite <- HeqL in HeqR by lia.
    replace op with join in HeqR by auto.
    apply lattice_le_antisym.
    apply meet_inf.
    rewrite HeqR. apply join_le.
    subst L Q. apply join_b_preserves_le. intros.
    apply meet_ge.
    rewrite HeqR. rewrite meet_comm.
    rewrite meet_distr.
    apply join_sup. rewrite meet_comm. apply meet_ge.
    rewrite <- meet_comm.
    rewrite <- join_b_distr_ext with (f := fun j => (t j ⊓ meet_i 0 j s) ⊓ Q).
    apply join_b_sup. intros.
    rewrite HeqQ. rewrite meet_assoc.
    transitivity (meet_i 0 a0 s ⊓ join_b 0 K t). rewrite meet_comm. apply meet_ge.
    rewrite meet_comm.
    rewrite <- join_b_distr_ext with (f := fun j => t j ⊓ meet_i 0 a0 s).
    apply join_b_sup. intros.
    rewrite HeqL. transitivity (t a1 ⊓ meet_i 0 a1 s).
    { apply meet_preserves_ge. reflexivity. unfold meet_i at 1.
      replace a0 with (a1 + (a0 - a1)) by lia. rewrite op_i_app.
      simpl. fold meet_i. apply meet_ge.
    }
    pose proof (join_b_le 0 K (fun j => t j ⊓ meet_i 0 j s) a1 ltac:(lia) ltac:(lia)).
    apply H4.
    auto.
    lia.
    auto.
    lia.
  }
Qed.

Lemma sinceDual_always_bounded :
  forall (ϕ ψ : Formula A) τ a i,
    infRobustness (FSinceDual 0 a ϕ ψ) τ i
    = infRobustness (FOr (FSinceDualUnbounded 0 ϕ ψ) (FAlways 0 a ψ)) τ i.
Proof.
  intros. simpl.
  remember (min i a) as K.
  pose (t := fun j => infRobustness ψ τ (i - j)).
  pose (s := fun j => infRobustness ϕ τ (i - j)).
  fold s. fold t. under meet_b_ext => j.
  replace (infRobustness _ _ _) with (t j) by auto.
  over. under [in RHS]meet_b_ext => j.
  replace (infRobustness _ _ _) with (t j) by auto.
  over.
  remember (meet_b 0 K (fun j : nat => t j ⊔ join_i 0 j s)) as L.
  remember (meet_b 0 K t) as Q.
  remember (meet_b 0 i (fun j : nat => t j ⊔ join_i 0 j s)) as R.
  destruct (Compare_dec.dec_le i a).
  { replace (min i a) with i in HeqK by lia. subst K.
    rewrite <- HeqL in HeqR. subst R. apply lattice_le_antisym.
    apply join_le. apply join_sup. reflexivity.
    subst L Q. apply meet_b_preserves_ge. intros.
    apply join_le.
  }
  { unfold meet_b in HeqR. rewrite -> op_b_app with (hi1 := K) in HeqR by lia.
    fold meet_b in HeqR. rewrite <- HeqL in HeqR by lia.
    replace op with meet in HeqR by auto.
    apply lattice_le_antisym.
    { rewrite HeqR. rewrite join_comm.
      rewrite join_distr.
      apply meet_inf. rewrite join_comm. apply join_le.
      rewrite <- join_comm.
      rewrite <- meet_b_distr_ext with (f := fun j => (t j ⊔ join_i 0 j s) ⊔ Q).
      apply meet_b_inf. intros.
      rewrite HeqQ. rewrite join_assoc.
      transitivity (join_i 0 a0 s ⊔ meet_b 0 K t).
      {
       rewrite join_comm.
       rewrite <- meet_b_distr_ext with (f := fun j => t j ⊔ join_i 0 a0 s).
       apply meet_b_inf. intros.
       rewrite HeqL. transitivity (t a1 ⊔ join_i 0 a1 s).
       { pose proof (meet_b_ge 0 K (fun j => t j ⊔ join_i 0 j s) a1 ltac:(lia) ltac:(lia)).
         apply H4. }
       { apply join_preserves_le. reflexivity. unfold join_i at 2.
      replace a0 with (a1 + (a0 - a1)) by lia. rewrite op_i_app.
      simpl. fold join_i. apply join_le. }
      auto.
       lia.
      }
      { replace ((join (t a0) (join (join_i O a0 s) (meet_b O K t))))
          with ((join (join (join_i O a0 s) (meet_b O K t)) (t a0)))
          by now rewrite join_comm.
        apply join_le. }
    auto.
    lia. }
    { apply join_sup.
      rewrite HeqR. apply meet_ge.
      subst L Q. apply meet_b_preserves_ge. intros.
      apply join_le. }
  }
Qed.

End LemmaThirteen.
