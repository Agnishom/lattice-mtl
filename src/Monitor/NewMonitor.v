Require Import Coq.Lists.List.

From Algebra Require Import Monoid.
From Algebra Require Import Lattice.
From Syntax Require Import Formula.
From Semantics Require Import Robustness.
From Semantics Require Import InfRobustness.
From NonEmptyList Require Import NonEmptyList.
Require Import Mealy.
Require Import Monitor.
From Lemmas Require Import Lemmas.

Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import ssreflect.

Section NewMonitor.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition monSinceUp (n : nat) : @Monitor Val (Val * Val) :=
  @monAnd Val (Val * Val) lattice_val
    (monSince (monAtomic fst) (monAtomic snd))
    (monSometimeBounded n (monAtomic snd)).

Lemma monSinceUp_correcntess:
  forall n, implements (monSinceUp n) (FSince 0 n (FAtomic fst) (FAtomic snd)).
Proof.
  unfold implements. intros.
  remember (FSince _ _ _ _) as f.
  rewrite -> robustness_eq with (ψ := normalize f) by now apply normalize_correctness.
  subst. simpl. unfold monSinceUp.
  apply monAnd_correctness.
  - apply monSince_correctness. auto.
    apply monAtomic_correctness.
    apply monAtomic_correctness.
  - apply monSometimeBounded_correctness.
    apply monAtomic_correctness.
Qed.

Lemma fst_extend_neZip1 {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
      neLength σ = neLength τ
      -> forall i, neLength σ <= i
             -> fst (nth i (rev (toList (neZip σ τ))) (latest (neZip σ τ))) = nth i (rev (toList σ)) (latest σ).
Proof.
  intros.
  rewrite nth_overflow.
  rewrite rev_length. rewrite length_toList.
  rewrite neZip_neLength. auto.
  congruence.
  rewrite nth_overflow.
  rewrite rev_length. rewrite length_toList.
  auto.
  destruct τ; destruct σ; auto.
Qed.

Lemma snd_extend_neZip1 {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
      neLength σ = neLength τ
      -> forall i, neLength τ <= i
             -> snd (nth i (rev (toList (neZip σ τ))) (latest (neZip σ τ))) = nth i (rev (toList τ)) (latest τ).
Proof.
  intros.
  rewrite nth_overflow.
  rewrite rev_length. rewrite length_toList.
  rewrite neZip_neLength. auto.
  congruence.
  rewrite nth_overflow.
  rewrite rev_length. rewrite length_toList.
  auto.
  destruct τ; destruct σ; auto.
Qed.

Lemma fst_extend_neZip2 {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
      neLength σ = neLength τ
      -> forall i, neLength σ > i
             -> forall d1 d2, fst (nth i (rev (toList (neZip σ τ))) d1) = nth i (rev (toList σ)) d2.
Proof.
  intros.
  destruct σ as [σ0 | σ σ0];
    destruct τ as [τ0 | τ τ0].
  {
    simpl in *. destruct i; auto. lia.
  }
  {
    simpl in H.
    rewrite <- length_toList in H.
    pose proof (length_toList1 τ). lia.
  }
  {
    simpl in H.
    rewrite <- length_toList in H.
    pose proof (length_toList1 σ). lia.
  }
  {
    simpl latest.
    rewrite rev_nth.
    {
      simpl in *. rewrite length_toList. inversion H.
      rewrite -> neZip_neLength by assumption.
      lia.
    }
    rewrite -> rev_nth by
        now rewrite length_toList.
    simpl in H. inversion H. clear H.
    simpl neZip. simpl toList. simpl length.
    simpl in H0.
    rewrite -> length_toList at 1.
    rewrite -> neZip_neLength by assumption.
    rewrite <- length_toList.
    replace (S (length (toList σ)) - S i) with (length (toList σ) - i)
      by now rewrite <- length_toList in H0; lia.
    remember (length (toList σ) - i) as j.
    remember (length (toList σ)) as nT.
    rewrite <- length_toList in H0. rewrite <- HeqnT in H0.
    rewrite <- (length_toList σ) in H2. rewrite <- HeqnT in H2.
    revert σ0 τ0.
    generalize dependent σ. generalize dependent τ.
    generalize dependent nT. generalize dependent i.
    induction j.
    {
      auto.
    }
    {
      intros. simpl.
      clear σ0 τ0.
      destruct σ as [σ0 | σ σ0];
        destruct τ as [τ0 | τ τ0].
      {
        simpl in *. destruct j; auto. lia.
      }
      {
        simpl in H2, HeqnT.
        rewrite <- length_toList in H2.
        pose proof (length_toList1 τ). lia.
      }
      {
        simpl in H2, HeqnT.
        pose proof (length_toList1 σ). lia.
      }
      {
        simpl neZip. simpl toList.
        simpl in HeqnT. apply IHj with (nT := (length (toList σ))) (i := (length (toList σ)) - j).
        lia. lia. simpl in *. lia. auto.
      }
    }
  }
Qed.

Lemma snd_extend_neZip2 {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
      neLength σ = neLength τ
      -> forall i, neLength τ > i
             -> forall d1 d2, snd (nth i (rev (toList (neZip σ τ))) d1) = nth i (rev (toList τ)) d2.
Proof.
  intros.
  destruct σ as [σ0 | σ σ0];
    destruct τ as [τ0 | τ τ0].
  {
    simpl in *. destruct i; auto. lia.
  }
  {
    simpl in H.
    rewrite <- length_toList in H.
    pose proof (length_toList1 τ). lia.
  }
  {
    simpl in H.
    rewrite <- length_toList in H.
    pose proof (length_toList1 σ). lia.
  }
  {
    simpl latest.
    rewrite rev_nth.
    {
      simpl in *. rewrite length_toList. inversion H.
      rewrite -> neZip_neLength by assumption.
      lia.
    }
    rewrite -> rev_nth by
        now rewrite length_toList.
    simpl in H. inversion H. clear H.
    simpl neZip. simpl toList. simpl length.
    simpl in H0.
    rewrite -> length_toList at 1.
    rewrite -> neZip_neLength by assumption.
    rewrite H2. rewrite <- length_toList.
    replace (S (length (toList τ)) - S i) with (length (toList τ) - i)
      by now rewrite <- length_toList in H0; lia.
    remember (length (toList τ) - i) as j.
    remember (length (toList τ)) as nT.
    rewrite <- length_toList in H0. rewrite <- HeqnT in H0.
    rewrite <- (length_toList τ) in H2. rewrite <- HeqnT in H2.
    revert σ0 τ0.
    generalize dependent σ. generalize dependent τ.
    generalize dependent nT. generalize dependent i.
    induction j.
    {
      auto.
    }
    {
      intros. simpl.
      clear σ0 τ0.
      destruct σ as [σ0 | σ σ0];
        destruct τ as [τ0 | τ τ0].
      {
        simpl in *. destruct j; auto. lia.
      }
      {
        simpl in H2, HeqnT.
        pose proof (length_toList1 τ). lia.
      }
      {
        simpl in H2, HeqnT.
        rewrite <- length_toList in H2.
        pose proof (length_toList1 σ). lia.
      }
      {
        simpl neZip. simpl toList.
        simpl in HeqnT. apply IHj with (nT := (length (toList τ))) (i := (length (toList τ)) - j).
        lia. lia. auto. simpl in *. lia.
      }
    }
  }
Qed.


Lemma fst_extend_neZip {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
  neLength σ = neLength τ
  -> forall i, fst (extend (neZip σ τ) i) = extend σ i.
Proof.
  intros.
  unfold extend.
  destruct (Compare_dec.le_lt_dec (neLength σ) i) as [Hti | Hti].
  + auto using fst_extend_neZip1.
  + auto using fst_extend_neZip2.
Qed.

Lemma snd_extend_neZip {X Y : Type} (σ : nonEmpty X) (τ : nonEmpty Y):
  neLength σ = neLength τ
  -> forall i, snd (extend (neZip σ τ) i) = extend τ i.
Proof.
  intros.
  unfold extend.
  destruct (Compare_dec.le_lt_dec (neLength τ) i) as [Hti | Hti].
  + auto using snd_extend_neZip1.
  + auto using snd_extend_neZip2.
Qed.

Lemma monSinceUp_composition (m n : Monitor) (ϕ ψ : Formula A):
  implements m ϕ
  -> implements n ψ
  -> forall a, implements ((mPar m n) >> monSinceUp a) (FSince 0 a ϕ ψ).
Proof.
  unfold implements.
  intros.
  rewrite mPar_mCompose.
  rewrite monSinceUp_correcntess.
  unfold robustness. simpl.
  rewrite length_toList.
  rewrite -> neZip_neLength
    by now repeat rewrite gCollect_neLength; auto.
  rewrite gCollect_neLength.
  rewrite length_toList.
  under join_b_ext_in => j.
  rewrite -> snd_extend_neZip
    by now repeat rewrite gCollect_neLength; auto.
  intros.
  rewrite -> (extend_gCollect Val A) with (ϕ0 := ψ).
  under meet_i_ext_in => k.
  intros. rewrite -> fst_extend_neZip
    by now repeat rewrite gCollect_neLength; auto.
  rewrite -> (extend_gCollect Val A) with (ϕ0 := ϕ).
  over.
  auto.
  rewrite <- length_toList. pose proof (length_toList1 σ). lia.
  over.
  auto.
  rewrite <- length_toList. pose proof (length_toList1 σ). lia.
  auto.
Qed.


End NewMonitor.
