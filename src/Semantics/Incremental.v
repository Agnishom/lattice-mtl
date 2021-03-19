(**

This file contains several lemmas which legitimize the incremental computation of certain formulas.
In other words, given a formula ϕ and a position i, they describe how [infRobustness ϕ i] can be used to evaluate [infRobustness ϕ (i + 1)].

*)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import ssreflect.

From Algebra Require Import Lattice.
From Algebra Require Import Monoid.
From Syntax Require Import Formula.

Require Import InfRobustness.
Require Import SimpleProperties.
Require Import Equivalences.

Section Incremental.

Generalizable Variables Val lattice_val boundedLattice_val distributiveLattice_val.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Definition Trace := nat -> A.

Lemma since_incremental :
  forall (ϕ ψ : Formula A) τ i,
    infRobustness (FSinceUnbounded 0 ϕ ψ) τ (S i)
    = ((infRobustness ψ τ (S i))
        ⊔ (infRobustness (FSinceUnbounded 0 ϕ ψ) τ i
          ⊓ infRobustness ϕ τ (S i))).
Proof.
  intros. remember (S i) as i0. simpl infRobustness at 1.
  unfold join_b. rewrite Heqi0.
  replace (S i) with (1 + i) at 1 by lia.
  rewrite ->op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. unfold op_i at 1.
  unfold meet_i at 1. unfold op_i.
  simpl finite_op.
  unfold finite_op at 1 2. simpl List.fold_left.
  rewrite join_bottom_l. rewrite meet_top_r.
  f_equal.
  replace 1 with (0 + 1) at 1 by lia.
  replace (1 + i) with (i + 1) by lia.
  rewrite <-op_b_shift_ext_in
    with
      (g := (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k))))
      (h := 1)
    by now intros; f_equal; f_equal; lia.
  replace ( (op_b Val 0 i
                  (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) )
    with ( (join_b 0 i
                   (fun j : nat => infRobustness ψ τ (i - j) ⊓ meet_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) ) by auto.
  under join_b_ext_in => j.
  intros.
  replace (S j) with (1 + j) at 1 by lia.
  unfold meet_i.
  rewrite ->op_i_app with (l1 := 1).
  unfold op_i at 1. simpl finite_op.
  unfold finite_op. simpl List.fold_left.
  rewrite meet_top_l.
  rewrite <-op_i_shift_ext with
      (g :=(fun k : nat => infRobustness ϕ τ (i - k)))
    by now intros; f_equal; lia.
  replace (op (infRobustness ϕ τ (S i)) (op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) )
    with
      ((op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) ⊓ (infRobustness ϕ τ (S i)))
    by now simpl; rewrite meet_comm.
  rewrite <- meet_assoc.
  over.
  rewrite ->join_b_distr_ext_in with
  (g := (fun j : nat =>
           (infRobustness ψ τ (i - j) ⊓ op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k)))))
  (v := infRobustness ϕ τ (S i)) by now auto; lia.
  auto.
Qed.

Lemma sinceDual_incremental :
  forall (ϕ ψ : Formula A) τ i,
    infRobustness (FSinceDualUnbounded 0 ϕ ψ) τ (S i)
    = ((infRobustness ψ τ (S i))
        ⊓ (infRobustness (FSinceDualUnbounded 0 ϕ ψ) τ i
          ⊔ infRobustness ϕ τ (S i))).
Proof.
  intros. remember (S i) as i0. simpl infRobustness at 1.
  unfold meet_b. rewrite Heqi0.
  replace (S i) with (1 + i) at 1 by lia.
  rewrite ->op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. unfold op_i at 1.
  unfold join_i at 1. unfold op_i.
  simpl finite_op.
  unfold finite_op at 1 2. simpl List.fold_left.
  rewrite meet_top_l. rewrite join_bottom_r.
  f_equal.
  replace 1 with (0 + 1) at 1 by lia.
  replace (1 + i) with (i + 1) by lia.
  rewrite <-op_b_shift_ext_in
    with
      (g := (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k))))
      (h := 1)
    by now intros; f_equal; f_equal; lia.
  replace ( (op_b Val 0 i
                  (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) )
    with ( (meet_b 0 i
                   (fun j : nat => infRobustness ψ τ (i - j) ⊔ join_i 0 (S j) (fun k : nat => infRobustness ϕ τ (S i - k)))) ) by auto.
  under meet_b_ext_in => j.
  intros.
  replace (S j) with (1 + j) at 1 by lia.
  unfold join_i.
  rewrite ->op_i_app with (l1 := 1).
  unfold op_i at 1. simpl finite_op.
  unfold finite_op. simpl List.fold_left.
  rewrite join_bottom_l.
  rewrite <-op_i_shift_ext with
      (g :=(fun k : nat => infRobustness ϕ τ (i - k)))
    by now intros; f_equal; lia.
  replace (op (infRobustness ϕ τ (S i)) (op_i Val 0 j (fun k : nat => infRobustness ϕ τ (i - k))) )
    with
      ((@op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  0 j (fun k : nat => infRobustness ϕ τ (i - k))) ⊔ (infRobustness ϕ τ (S i)))
    by now simpl; rewrite join_comm.
  rewrite <- join_assoc.
  over.
  rewrite ->meet_b_distr_ext_in with
  (g := (fun j : nat =>
           (infRobustness ψ τ (i - j) ⊔ @op_i Val (@joinMonoid Val lattice_val lattice_val boundedLattice_val)  0 j (fun k : nat => infRobustness ϕ τ (i - k)))))
  (v := infRobustness ϕ τ (S i)) by now auto; lia.
  auto.
Qed.

Lemma sometimeUnbounded_incremental :
  forall (ϕ : Formula A) τ i,
    infRobustness (FSometimeUnbounded 0 ϕ) τ (S i)
    = ((infRobustness (FSometimeUnbounded 0 ϕ) τ i) ⊔ (infRobustness ϕ τ (S i))).
Proof.
  intros.
  replace (infRobustness (FSometimeUnbounded 0 ϕ) τ (S i)) with
      (join_b 0 (S i) (fun j => (infRobustness ϕ τ ((S i) - j)))) by auto.
  unfold join_b. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto. unfold op_i.
  simpl finite_op. rewrite finite_op_singleton.
  replace 1 with (0 + 1) by lia. replace (S i) with (i + 1) by lia.
  rewrite <- op_b_shift.
  rewrite <- join_comm.
  enough
    ((@op_b Val joinMonoid 0 i (fun i0 : nat => infRobustness ϕ τ (i + 1 - (i0 + 1))))
     = infRobustness (FSometimeUnbounded 0 ϕ) τ i) by now rewrite H.
  under op_b_ext => i0. replace (i + 1 - (i0 + 1)) with (i - i0) by lia. over.
  auto.
Qed.

Lemma alwaysUnbounded_incremental :
  forall (ϕ : Formula A) τ i,
    infRobustness (FAlwaysUnbounded 0 ϕ) τ (S i)
    = ((infRobustness (FAlwaysUnbounded 0 ϕ) τ i) ⊓ (infRobustness ϕ τ (S i))).
Proof.
  intros.
  replace (infRobustness (FAlwaysUnbounded 0 ϕ) τ (S i)) with
      (meet_b 0 (S i) (fun j => (infRobustness ϕ τ ((S i) - j)))) by auto.
  unfold meet_b. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto. unfold op_i.
  simpl finite_op. rewrite finite_op_singleton.
  replace 1 with (0 + 1) by lia. replace (S i) with (i + 1) by lia.
  rewrite <- op_b_shift.
  rewrite <- meet_comm.
  enough
    ((@op_b Val meetMonoid 0 i (fun i0 : nat => infRobustness ϕ τ (i + 1 - (i0 + 1))))
     = infRobustness (FAlwaysUnbounded 0 ϕ) τ i) by now rewrite H.
  under op_b_ext => i0. replace (i + 1 - (i0 + 1)) with (i - i0) by lia. over.
  auto.
Qed.

Lemma sometimeBounded_incremental :
  forall (ϕ : Formula A) τ n i,
    infRobustness (FSometime 0 (S n) ϕ) τ (S i)
    = ((infRobustness (FSometime 0 n ϕ) τ i) ⊔ infRobustness ϕ τ (S i)).
Proof.
  intros.
  replace (infRobustness (FSometime 0 (S n) ϕ) τ (S i))
    with (join_b 0 (S (min i n)) (fun j : nat => infRobustness ϕ τ (S i - j))) by auto.
  simpl infRobustness at 2.
  unfold join_b at 1. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto.
  unfold op_i. simpl List.map. rewrite finite_op_singleton.
  rewrite join_comm.
  replace 1 with (0 + 1) by lia. replace (S (min i n)) with (min i n + 1) by lia.
  rewrite <- op_b_shift_ext with (h := 1) (g := (fun j : nat => infRobustness ϕ τ ( i - j))).
  auto.
  intros. f_equal. lia.
Qed.

Lemma alwaysBounded_incremental :
  forall (ϕ : Formula A) τ n i,
    infRobustness (FAlways 0 (S n) ϕ) τ (S i)
    = ((infRobustness (FAlways 0 n ϕ) τ i) ⊓ infRobustness ϕ τ (S i)).
Proof.
  intros.
  replace (infRobustness (FAlways 0 (S n) ϕ) τ (S i))
    with (meet_b 0 (S (min i n)) (fun j : nat => infRobustness ϕ τ (S i - j))) by auto.
  simpl infRobustness at 2.
  unfold meet_b at 1. rewrite -> op_b_app with (hi1 := 0) by lia.
  unfold op_b at 1. replace (1 - 0) with 1 by auto.
  unfold op_i. simpl List.map. rewrite finite_op_singleton.
  rewrite meet_comm.
  replace 1 with (0 + 1) by lia. replace (S (min i n)) with (min i n + 1) by lia.
  rewrite <- op_b_shift_ext with (h := 1) (g := (fun j : nat => infRobustness ϕ τ ( i - j))).
  auto.
  intros. f_equal. lia.
Qed.

End Incremental.
