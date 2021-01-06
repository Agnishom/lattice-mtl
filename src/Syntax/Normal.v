Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Require Import Formula.
From Algebra Require Import Lattice.

Section Normal.

Variable (Val : Type).
Variable (A : Type).
Context {lattice_val : Lattice Val}.
Context {boundedLattice_val : BoundedLattice Val}.
Context {distributiveLattice_val : DistributiveLattice Val}.

Inductive isNormal : @Formula Val A -> Prop :=
| NAtomic : forall f, isNormal (FAtomic f)
| NOr : forall α β, isNormal α -> isNormal β -> isNormal (FOr α β)
| NAnd : forall α β, isNormal α -> isNormal β -> isNormal (FAnd α β)
| NDelay : forall α i, isNormal α -> isNormal (FDelay i α)
| NDelayDual : forall α i, isNormal α -> isNormal (FDelayDual i α)
| NSometimeBounded : forall α i, isNormal α -> isNormal (FSometime 0 (S i) α)
| NAlwaysBounded : forall α i, isNormal α -> isNormal (FAlways 0 (S i) α)
| NSometimeUnbounded : forall α, isNormal α -> isNormal (FSometimeUnbounded 0 α)
| NAlwaysUnbounded : forall α, isNormal α -> isNormal (FAlwaysUnbounded 0 α)
| NSinceUnbounded : forall α β, isNormal α ->  isNormal β -> isNormal (FSinceUnbounded 0 α β)
| NSinceDualUnbounded : forall α β, isNormal α -> isNormal β -> isNormal (FSinceDualUnbounded 0 α β)
.


Fixpoint normalize (ϕ : @Formula Val A) :=
  match ϕ with
  | FAtomic f => FAtomic f
  | FAnd α β => FAnd (normalize α) (normalize β)
  | FOr α β => FOr (normalize α) (normalize β)

  | FSometime 0 i α => FSometime 0 i (normalize α)
  | FAlways 0 i α => FAlways 0 i (normalize α)
  | FSometimeUnbounded 0 α => FSometimeUnbounded 0 (normalize α)
  | FAlwaysUnbounded 0 α => FAlwaysUnbounded 0 (normalize α)
  | FSinceUnbounded 0 α β => FSinceUnbounded 0 (normalize α) (normalize β)
  | FSinceDualUnbounded 0 α β => FSinceDualUnbounded 0 (normalize α) (normalize β)
  | FSometime ((S i') as i) j α =>
    match (i =? j) with
    | true => FSometime i j (normalize α)
    | false => match (i <? j) with
              | false => FAtomic (fun _ => bottom)
              | true => FDelay i (FSometime 0 (j - i) (normalize α))
              end
    end
  | FAlways ((S i') as i) j α =>
    match (i =? j) with
    | true => FAlways i j (normalize α)
    | false => match (i <? j) with
              | false => FAtomic (fun _ => top)
              | true => FDelayDual i (FAlways 0 (j - i) (normalize α))
              end
    end
  | FSometimeUnbounded ((S i') as i) α => FDelay i (FSometimeUnbounded 0 (normalize α))
  | FAlwaysUnbounded ((S i') as i) α => FDelayDual i (FAlwaysUnbounded 0 (normalize α))
  | FSinceUnbounded ((S i') as i) α β =>
    FAnd (FDelay i (FSinceUnbounded 0 (normalize α) (normalize β))) (FAlways 0 i' (normalize α))
  | FSinceDualUnbounded  ((S i') as i) α β =>
    FOr (FDelayDual i (FSinceDualUnbounded 0 (normalize α) (normalize β))) (FSometime 0 i' (normalize α))
  | FSince 0 i α β => FAnd (FSinceUnbounded 0 (normalize α) (normalize β)) (FSometime 0 i (normalize β))
  | FSinceDual 0 i α β => FOr (FSinceDualUnbounded 0 (normalize α) (normalize β)) (FAlways 0 i (normalize β))
  | FSince ((S i') as i) j α β =>
    match (i' <? j) with
    | false => FAtomic (fun _ => bottom)
    | true => FAnd (FDelay i (FAnd (FSinceUnbounded 0 (normalize α) (normalize β)) (FSometime 0 (j - i) (normalize β)))) (FAlways 0 i' (normalize α))
    end
  | FSinceDual ((S i') as i) j α β =>
    match (i' <? j) with
    | false => FAtomic (fun _ => top)
    | true => FOr (FDelayDual i (FOr (FSinceDualUnbounded 0 (normalize α) (normalize β)) (FAlways 0 (j - i) (normalize β)))) (FSometime 0 i' (normalize α))
    end
  end.

Lemma isNormal_normalize :
  forall ϕ, isNormal (normalize ϕ).
Proof.
  induction ϕ.
  - apply NAtomic.
  - simpl. now apply NAnd.
  - simpl. now apply NOr.
  - simpl. destruct n.
    + destruct n0.
      ++ now apply NDelay.
      ++ now apply NSometimeBounded.
    + destruct (S n =? n0) eqn:E.
      ++ apply EqNat.beq_nat_true in E. rewrite E.
         now apply NDelay.
      ++ destruct (S n <? n0) eqn:EE.
         +++ apply Nat.ltb_lt in EE.
         destruct (n0 - S n) eqn:F. lia.
         apply NDelay. now apply NSometimeBounded.
         +++ apply NAtomic.
  - simpl. destruct n.
    + destruct n0.
      ++ now apply NDelayDual.
      ++ now apply NAlwaysBounded.
    + destruct (S n =? n0) eqn:E.
      ++ apply EqNat.beq_nat_true in E. rewrite E.
         now apply NDelayDual.
      ++ destruct (S n <? n0) eqn:EE.
         +++ apply Nat.ltb_lt in EE.
         destruct (n0 - S n) eqn:F. lia.
         apply NDelayDual. now apply NAlwaysBounded.
         +++ apply NAtomic.
  - simpl. destruct n.
    + now apply NSometimeUnbounded.
    + apply NDelay. now apply NSometimeUnbounded.
  - simpl. destruct n.
    + now apply NAlwaysUnbounded.
    + apply NDelayDual. now apply NAlwaysUnbounded.
  - simpl. destruct n.
    + apply NAnd.
      now apply NSinceUnbounded.
      destruct n0.
      ++ now apply NDelay.
      ++ now apply NSometimeBounded.
    + destruct (n <? n0) eqn:E.
      ++ rewrite -> Nat.ltb_lt in E.
         apply NAnd. apply NDelay.
         apply NAnd. now apply NSinceUnbounded.
         destruct (n0 - S n) eqn:EE.
         +++ now apply NDelay.
         +++ now apply NSometimeBounded.
         +++ destruct n.
             ++++ now apply NDelayDual.
             ++++ now apply NAlwaysBounded.
      ++ apply NAtomic.
  - simpl. destruct n.
    + apply NOr.
      now apply NSinceDualUnbounded.
      destruct n0.
      ++ now apply NDelayDual.
      ++ now apply NAlwaysBounded.
    + destruct (n <? n0) eqn:E.
      ++ rewrite -> Nat.ltb_lt in E.
         apply NOr. apply NDelayDual.
         apply NOr. now apply NSinceDualUnbounded.
         destruct (n0 - S n) eqn:EE.
         +++ now apply NDelayDual.
         +++ now apply NAlwaysBounded.
         +++ destruct n.
             ++++ now apply NDelay.
             ++++ now apply NSometimeBounded.
      ++ apply NAtomic.
  - simpl. destruct n.
    + now apply NSinceUnbounded.
    + apply NAnd. apply NDelay.
      now apply NSinceUnbounded.
      destruct n.
      ++ now apply NDelayDual.
      ++ now apply NAlwaysBounded.
  - simpl. destruct n.
    + now apply NSinceDualUnbounded.
    + apply NOr. apply NDelayDual.
      now apply NSinceDualUnbounded.
      destruct n.
      ++ now apply NDelay.
      ++ now apply NSometimeBounded.
Qed.

End Normal.

Arguments isNormal {Val A}.
Arguments normalize {Val A lattice_val boundedLattice_val}.
