Require Import Monoid.
Require Import MTLTactics.

Require Import Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Import ListNotations.

Class Lattice A :=
  {
  join : A -> A -> A;
  meet : A -> A -> A;
  join_comm : forall x y, join x y = join y x;
  meet_comm : forall x y, meet x y = meet y x;
  join_assoc : forall x y z, join (join x y) z = join x (join y z);
  meet_assoc : forall x y z, meet (meet x y) z = meet x (meet y z);
  absorb1 : forall x y, join x (meet x y) = x;
  absorb2 : forall x y, meet x (join x y) = x;
  }.


Infix "⊓" := meet (at level 85, right associativity).
Infix "⊔" := join (at level 80, right associativity).

Generalizable All Variables.

Lemma join_idempotent `{Lattice} : forall x, x = (x ⊔ x).
Proof.
  intros. rewrite <- absorb2 with (y := x) at 3. rewrite absorb1. reflexivity.
Qed.

Lemma meet_idempotent `{Lattice} : forall x, x = (x ⊓ x).
Proof.
  intros. rewrite <- absorb1 with (y := x) at 3. rewrite absorb2. reflexivity.
Qed.

Definition lattice_le {A : Type} `{Lattice A} (a b : A) : Prop := (a ⊓ b) = a.

Infix "⊑" := lattice_le (at level 80, no associativity).

Lemma lattice_le_alternate {A : Type} `{Lattice A} : forall a b, a ⊑ b <-> (a ⊔ b) = b.
Proof.
  unfold lattice_le. split; intros.
  + rewrite <- absorb1 with (y := a). rewrite meet_comm. rewrite H0. now rewrite join_comm.
  + rewrite <- absorb2 with (y := b). now rewrite H0.
Qed.


Class BoundedLattice A `{Lattice A}:=
  {
  bottom : A;
  top : A;
  join_bottom_r : forall x, (x ⊔ bottom) = x;
  meet_top_r : forall x, (x ⊓ top) = x;
  }.

Lemma join_bottom_l `{BoundedLattice} : forall x, (bottom ⊔ x) = x.
Proof.
  intros. rewrite join_comm. now rewrite join_bottom_r.
Qed.

Lemma meet_top_l `{BoundedLattice} : forall x, (top ⊓ x) = x.
Proof.
  intros. rewrite meet_comm. now rewrite meet_top_r.
Qed.

Lemma join_top_l `{BoundedLattice} : forall x, (top ⊔ x) = top.
Proof.
  intros. rewrite <- meet_top_l with (x0 := x). now rewrite absorb1.
Qed.

Lemma join_top_r `{BoundedLattice} : forall x, (x ⊔ top) = top.
Proof.
  intros. rewrite join_comm. now rewrite join_top_l.
Qed.

Lemma meet_bottom_l `{BoundedLattice} : forall x, (bottom ⊓ x) = bottom.
Proof.
  intros. rewrite <- join_bottom_l with (x0 := x). now rewrite absorb2.
Qed.

Lemma meet_bottom_r `{BoundedLattice} : forall x, (x ⊓ bottom) = bottom.
Proof.
  intros. rewrite meet_comm. now rewrite meet_bottom_l.
Qed.

Definition finite_meet {A : Type} `{Lattice A} `{BoundedLattice A} : list A -> A :=
  fun l => fold_left meet l top.

Definition finite_join {A : Type} `{Lattice A} `{BoundedLattice A} : list A -> A :=
  fun l => fold_left join l bottom.

Lemma finite_join_app {A : Type} `{Lattice A} `{BoundedLattice A} :
  forall (xs ys : list A), finite_join (xs ++ ys) = (finite_join xs ⊔ finite_join ys).
Proof.
  unfold finite_join. intros. rewrite fold_left_app.
  induction ys using list_r_ind.
  - simpl. now rewrite join_bottom_r.
  - rewrite fold_left_app. simpl. rewrite IHys.
    rewrite fold_left_app. simpl. now rewrite join_assoc.
Qed.

Lemma finite_meet_app {A : Type} `{Lattice A} `{BoundedLattice A} :
  forall (xs ys : list A), finite_meet (xs ++ ys) = (finite_meet xs ⊓ finite_meet ys).
Proof.
  unfold finite_meet. intros. rewrite fold_left_app.
  induction ys using list_r_ind.
  - simpl. now rewrite meet_top_r.
  - rewrite fold_left_app. simpl. rewrite IHys.
    rewrite fold_left_app. simpl. now rewrite meet_assoc.
Qed.

Lemma finite_meet_top {A B : Type} `{Lattice A} `{BoundedLattice A} (xs : list B) :
  finite_meet (map (fun _ => top) xs) = top.
Proof.
  intros. induction xs.
  - auto.
  - simpl. replace (top :: map (fun _ : B => top) xs) with ([top] ++  map (fun _ : B => top) xs) by auto.
    rewrite finite_meet_app. rewrite IHxs. unfold finite_meet. simpl. now repeat rewrite meet_top_r.
Qed.

Lemma finite_join_bottom {A B : Type} `{Lattice A} `{BoundedLattice A} (xs : list B) :
  finite_join (map (fun _ => bottom) xs) = bottom.
Proof.
  intros. induction xs.
  - auto.
  - simpl. replace (bottom :: map (fun _ : B => bottom) xs) with ([bottom] ++  map (fun _ : B => bottom) xs) by auto.
   rewrite finite_join_app. rewrite IHxs. unfold finite_join. simpl. now repeat rewrite join_bottom_r.
Qed.


Class DistributiveLattice A `{Lattice A} :=
  {
  meet_distr : forall x y z, (x ⊓ (y ⊔ z)) = ((x ⊓ y) ⊔ (x ⊓ z));
  }.

Lemma join_distr `{DistributiveLattice} : forall x y z, (x ⊔ (y ⊓ z)) = ((x ⊔ y) ⊓ (x ⊔ z)).
Proof.
  intros. rewrite meet_distr. rewrite meet_comm with (x0 := x ⊔ y) (y0 := x). rewrite absorb2.
  rewrite meet_comm with (x0 := x ⊔ y). rewrite meet_distr. rewrite <- join_assoc.
  rewrite meet_comm with (x0 := z). rewrite absorb1. now rewrite meet_comm.
Qed.

Lemma finite_meet_distr {A B : Type}
      {_ : Lattice A} {_ : BoundedLattice A } {_ : DistributiveLattice A} (v : A) :
  forall (f : B -> A) (xs : list B) (x : B),
    finite_join (map (fun i => v ⊓ f i) (xs ++ [x])) = (v ⊓ (finite_join (map (fun i => f i) (xs ++ [x])))).
Proof.
  intros. generalize dependent x. induction xs using list_r_ind.
  - simpl. intros. unfold finite_join. simpl. now repeat rewrite join_bottom_l.
  - intros. rewrite map_app. rewrite finite_join_app.
    rewrite (map_app (fun i : B => f i)). simpl.
    rewrite IHxs. rewrite finite_join_app.
    rewrite meet_distr. unfold finite_join.
    simpl. now repeat rewrite join_bottom_l.
Qed.

Lemma finite_join_distr {A B : Type}
      {_ : Lattice A} {_ : BoundedLattice A } {_ : DistributiveLattice A} (v : A) :
  forall (f : B -> A) (xs : list B) (x : B),
    finite_meet (map (fun i => v ⊔ f i) (xs ++ [x])) = (v ⊔ (finite_meet (map (fun i => f i) (xs ++ [x])))).
Proof.
  intros. generalize dependent x. induction xs using list_r_ind.
  - simpl. intros. unfold finite_meet. simpl. now repeat rewrite meet_top_l.
  - intros. rewrite map_app. rewrite finite_meet_app.
    rewrite (map_app (fun i : B => f i)). simpl.
    rewrite IHxs. rewrite finite_meet_app.
    rewrite join_distr. unfold finite_meet.
    simpl. now repeat rewrite meet_top_l.
Qed.


Instance joinMonoid {A : Type} `{Lattice A} `{BoundedLattice A} : Monoid A :=
  {
  op := join;
  unit := bottom;
  op_unit_r := join_bottom_r;
  op_unit_l := join_bottom_l;
  op_assoc := ltac:(intros; now rewrite join_assoc);
  }.

Instance meetMonoid {A : Type} `{Lattice A} `{BoundedLattice A} : Monoid A :=
  {
  op := meet;
  unit := top;
  op_unit_r := meet_top_r;
  op_unit_l := meet_top_l;
  op_assoc := ltac:(intros; now rewrite meet_assoc);
  }.


Instance boolLattice : Lattice bool :=
  {
  join := orb;
  meet := andb;
  join_comm := orb_comm;
  meet_comm := andb_comm;
  join_assoc := ltac:(intros; now rewrite orb_assoc);
  meet_assoc := ltac:(intros; now rewrite andb_assoc);
  absorb1 := absorption_orb;
  absorb2 := absorption_andb;
  }.

Instance boolBoundedLattice : BoundedLattice bool:=
  {
  bottom := false;
  top := true;
  join_bottom_r := orb_false_r;
  meet_top_r := andb_true_r;
  }.

Instance boolDistributiveLattice : DistributiveLattice bool :=
  {
  meet_distr := andb_orb_distrib_r;
  }.
