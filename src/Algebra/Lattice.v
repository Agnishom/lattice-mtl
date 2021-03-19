(**

This file contains:

1. Definitions of Lattices.
  - The main defintion is given using an algebraic axiomatic approach.
  - An order relation is defined ⊑ using the lattice operations.
2. Several basic lemmas for both the axiomatic and the order theoretic approaches are proven.
  - In particular, we show the relationship between the binary operations and the endowed order.
3. Definition of Distibutive and Bounded Lattices.
4. Proof that The elements of a bounded lattice form a monoid either under ⊓ or ⊔
5. Proof that Boolean values form a bounded distributive lattice
6. Facts about ⊓ and ⊔ over finite lists.

 *)

Require Import Monoid.
From Lemmas Require Import Lemmas.

Require Import Lia.
Require Import Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import Relation_Definitions.

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

(** `finite_join l` stands for $\bigsqcup_{i \in l} i$ **)
(** `finite_meet l` stands for $\bigsqcap_{i \in l} i$ **)

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

(** `join_b lo hi f` stands for $\bigsqcup_{i=lo}^{hi} f(i)$ **)
(** `join_i start length f` stands for $\bot$ when `length` = 0,
otherwise it stands for $\bigsqcup_{i=start}^{start + length - 1} f(i)$ **)
(** similar convetions for meet **)

Definition join_i {A : Type} `{Lattice A} `{BoundedLattice A} : nat -> nat -> (nat -> A) -> A
  := (@op_i A joinMonoid ).

Definition meet_i {A : Type} `{Lattice A} `{BoundedLattice A} : nat -> nat -> (nat -> A) -> A
  := (@op_i A meetMonoid ).

Definition join_b {A : Type} `{Lattice A} `{BoundedLattice A} : nat -> nat -> (nat -> A) -> A
  := (@op_b A joinMonoid ).

Definition meet_b {A : Type} `{Lattice A} `{BoundedLattice A} : nat -> nat -> (nat -> A) -> A
  := (@op_b A meetMonoid ).

Lemma join_i_ext {A : Type} `{Lattice A} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
    : (forall a, f a = g a) -> join_i start length f = join_i start length g.
Proof.
    intros. unfold join_i. erewrite op_i_ext; easy.
Qed.

Lemma join_i_ext_in {A : Type} `{Lattice A} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
  : (forall a, start <= a -> a <= start + length -> f a = g a)
      -> join_i start length f = join_i start length g.
Proof.
  intros. unfold join_i. erewrite op_i_ext_in; easy.
Qed.

Lemma meet_i_ext {A : Type} `{Lattice A} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
    : (forall a, f a = g a) -> meet_i start length f = meet_i start length g.
Proof.
    intros. unfold meet_i. erewrite op_i_ext; easy.
Qed.

Lemma meet_i_ext_in {A : Type} `{Lattice A} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
  : (forall a, start <= a -> a <= start + length -> f a = g a)
      -> meet_i start length f = meet_i start length g.
Proof.
  intros. unfold meet_i. erewrite op_i_ext_in; easy.
Qed.

Lemma join_b_ext {A : Type} `{Lattice A} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
    : (forall a, f a = g a) -> join_b lo hi f = join_b lo hi g.
Proof.
    intros. unfold join_b. erewrite op_b_ext; easy.
Qed.

Lemma join_b_ext_in {A : Type} `{Lattice A} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
  : (forall a, lo <= a -> a <= hi -> f a = g a)
      -> join_b lo hi f = join_b lo hi g.
Proof.
  intros. unfold join_b. erewrite op_b_ext_in; easy.
Qed.

Lemma meet_b_ext {A : Type} `{Lattice A} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
    : (forall a, f a = g a) -> meet_b lo hi f = meet_b lo hi g.
Proof.
    intros. unfold meet_b. erewrite op_b_ext; easy.
Qed.

Lemma meet_b_ext_in {A : Type} `{Lattice A} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
  : (forall a, lo <= a -> a <= hi -> f a = g a)
      -> meet_b lo hi f = meet_b lo hi g.
Proof.
  intros. unfold meet_b. erewrite op_b_ext_in; easy.
Qed.

Lemma join_i_distr_ext {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (start length : nat) (f g : nat -> A) (v : A)
  : (forall a, f a = (g a ⊓ v))
    -> length > 0
    -> join_i start length f = ((join_i start length g) ⊓ v).
Proof.
  induction length.
  - intros. lia.
  - clear IHlength. intros. clear H0.
    induction length.
    + unfold join_i. unfold op_i. simpl. rewrite H.
      unfold finite_op. simpl. now repeat rewrite join_bottom_l.
    + unfold join_i in *. unfold op_i in *.
      remember (S length) as n.
      replace (S n) with (n + 1) by lia.
      rewrite seq_app. repeat rewrite map_app.
      repeat rewrite <- finite_op_app.
      rewrite IHlength. simpl. rewrite H.
      unfold finite_op at 2 4. simpl. repeat rewrite join_bottom_l.
      rewrite <- meet_comm at 1. rewrite <- meet_comm with (x := v).
      rewrite <- meet_distr with (x := v) (z := (g (start + n))) (y := finite_op A (map g (seq start n))).
      now rewrite meet_comm.
Qed.

Lemma join_i_distr_ext_in
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (start length : nat) (f g : nat -> A) (v : A)
  : (forall a, start <= a -> a <= start + length -> f a = (g a ⊓ v))
    -> length > 0
    -> join_i start length f = ((join_i start length g) ⊓ v).
Proof.
  intros. unfold join_i.
  rewrite op_i_ext_in with (g := fun a => g a ⊓ v) by auto.
  replace (op_i A start length (fun a : nat => g a ⊓ v))
    with (join_i start length (fun a : nat => g a ⊓ v) ) by auto.
  replace ((op_i A start length g ⊓ v))
          with ((join_i start length g ⊓ v)) by auto.
  now rewrite join_i_distr_ext with (g0 := g) (v0 := v).
Qed.

Lemma join_b_distr_ext
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (lo hi : nat) (f g : nat -> A) (v : A)
  : (forall a, f a = (g a ⊓ v))
    -> lo <= hi
    -> join_b lo hi f = ((join_b lo hi g) ⊓ v).
Proof.
  intros. unfold join_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f) with (join_i lo (S hi - lo) f) by auto.
  replace (op_i A lo (S hi - lo) g) with (join_i lo (S hi - lo) g) by auto.
  rewrite join_i_distr_ext with (g0 := g) (v0 := v); auto. lia.
Qed.

Lemma join_b_distr_ext_in
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (lo hi : nat) (f g : nat -> A) (v : A)
  : (forall a, lo <= a -> a <= hi -> f a = (g a ⊓ v))
    -> lo <= hi
    -> join_b lo hi f = ((join_b lo hi g) ⊓ v).
Proof.
  intros. unfold join_b.
  rewrite op_b_ext_in with (g := fun a => g a ⊓ v) by auto.
  replace (op_b A lo hi (fun a : nat => g a ⊓ v))
    with (join_b lo hi (fun a : nat => g a ⊓ v) ) by auto.
  replace ((op_b A _ _ g ⊓ v))
          with ((join_b lo hi g ⊓ v)) by auto.
  now rewrite join_b_distr_ext with (g0 := g) (v0 := v).
Qed.

Lemma meet_i_distr_ext {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (start length : nat) (f g : nat -> A) (v : A)
  : (forall a, f a = (g a ⊔ v))
    -> length > 0
    -> meet_i start length f = ((meet_i start length g) ⊔ v).
Proof.
  induction length.
  - intros. lia.
  - clear IHlength. intros. clear H0.
    induction length.
    + unfold meet_i. unfold op_i. simpl. rewrite H.
      unfold finite_op. simpl. now repeat rewrite meet_top_l.
    + unfold meet_i in *. unfold op_i in *.
      remember (S length) as n.
      replace (S n) with (n + 1) by lia.
      rewrite seq_app. repeat rewrite map_app.
      repeat rewrite <- finite_op_app.
      rewrite IHlength. simpl. rewrite H.
      unfold finite_op at 2 4. simpl. repeat rewrite meet_top_l.
      rewrite <- join_comm at 1. rewrite <- join_comm with (x := v).
      rewrite <- join_distr with (x := v) (z := (g (start + n))) (y := finite_op A (map g (seq start n))).
      now rewrite join_comm.
Qed.

Lemma meet_i_distr_ext_in
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (start length : nat) (f g : nat -> A) (v : A)
  : (forall a, start <= a -> a <= start + length -> f a = (g a ⊔ v))
    -> length > 0
    -> meet_i start length f = ((meet_i start length g) ⊔ v).
Proof.
  intros. unfold meet_i.
  rewrite op_i_ext_in with (g := fun a => g a ⊔ v) by auto.
  replace (op_i A start length (fun a : nat => g a ⊔ v))
    with (meet_i start length (fun a : nat => g a ⊔ v) ) by auto.
  replace ((op_i A start length g ⊔ v))
          with ((meet_i start length g ⊔ v)) by auto.
  now rewrite meet_i_distr_ext with (g0 := g) (v0 := v).
Qed.

Lemma meet_b_distr_ext
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (lo hi : nat) (f g : nat -> A) (v : A)
  : (forall a, f a = (g a ⊔ v))
    -> lo <= hi
    -> meet_b lo hi f = ((meet_b lo hi g) ⊔ v).
Proof.
  intros. unfold meet_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f) with (meet_i lo (S hi - lo) f) by auto.
  replace (op_i A lo (S hi - lo) g) with (meet_i lo (S hi - lo) g) by auto.
  rewrite meet_i_distr_ext with (g0 := g) (v0 := v); auto. lia.
Qed.

Lemma meet_b_distr_ext_in
      {A : Type} {X1 : Lattice A} {X2 : BoundedLattice A} {X3 :DistributiveLattice A}
      (lo hi : nat) (f g : nat -> A) (v : A)
  : (forall a, lo <= a -> a <= hi -> f a = (g a ⊔ v))
    -> lo <= hi
    -> meet_b lo hi f = ((meet_b lo hi g) ⊔ v).
Proof.
  intros. unfold meet_b.
  rewrite op_b_ext_in with (g := fun a => g a ⊔ v) by auto.
  replace (op_b A lo hi (fun a : nat => g a ⊔ v))
    with (meet_b lo hi (fun a : nat => g a ⊔ v) ) by auto.
  replace ((op_b A _ _ g ⊔ v))
          with ((meet_b lo hi g ⊔ v)) by auto.
  now rewrite meet_b_distr_ext with (g0 := g) (v0 := v).
Qed.

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

Instance lattice_le_refl {A : Type} `{Lattice A} : Reflexive lattice_le.
Proof.
  intros x. unfold lattice_le. auto using meet_idempotent.
Qed.

Instance lattice_le_trans {A : Type} `{Lattice A} : Transitive lattice_le.
Proof.
  intros x y z Hxy Hyz.
  unfold lattice_le in *.
  rewrite <- Hxy. rewrite meet_assoc.
  now rewrite -> Hyz.
Qed.

Instance lattice_le_antisym {A : Type} `{Lattice A}: Antisymmetric A eq lattice_le.
Proof.
  intros x y Hxy Hyx.
  unfold lattice_le in *.
  rewrite <- Hxy. rewrite <- Hyx at 2.
  now apply meet_comm.
Qed.

Instance lattice_le_preorder {A : Type} `{Lattice A} : PreOrder lattice_le.
Proof.
  split. apply lattice_le_refl. apply lattice_le_trans.
Qed.

Instance lattice_le_partialOrder {A : Type} `{Lattice A} : PartialOrder (@eq A) lattice_le.
Proof.
  intros x y. split.
  - intros. split.
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
  - intros. destruct H0.
    apply lattice_le_antisym; auto.
Qed.

Lemma lattice_ge_alternate {A : Type} `{Lattice A} : forall a b, a ⊑ b <-> (a ⊔ b) = b.
Proof.
  unfold lattice_le. split; intros.
  + rewrite <- H0. rewrite join_comm. rewrite meet_comm.
    now rewrite absorb1.
  + rewrite <- H0. now rewrite absorb2.
Qed.

Lemma bottom_le {A : Type} `{BoundedLattice A} :
  forall (x : A), bottom ⊑ x.
Proof.
  unfold lattice_le. apply meet_bottom_l.
Qed.

Lemma top_ge {A : Type} `{BoundedLattice A} :
  forall (x : A), x ⊑ top.
Proof.
  unfold lattice_le. apply meet_top_r.
Qed.

Lemma join_le {A : Type} `{Lattice A} : forall a b, a ⊑ (a ⊔ b).
Proof.
  unfold lattice_le.
  intros. now rewrite absorb2.
Qed.

Lemma meet_ge {A : Type} `{Lattice A} : forall a b, (a ⊓ b) ⊑ a.
Proof.
  unfold lattice_le.
  intros. rewrite meet_comm.
  rewrite <- meet_assoc. now rewrite <- meet_idempotent.
Qed.

Lemma join_sup {A : Type} `{Lattice A} :
  forall a b c,
    a ⊑ c
    -> b ⊑ c
    -> (a ⊔ b) ⊑ c.
Proof.
  intros a b c. repeat rewrite lattice_ge_alternate.
  intros. rewrite join_assoc. now rewrite H1.
Qed.

Lemma meet_inf {A : Type} `{Lattice A} :
  forall a b c,
    c ⊑ a
    -> c ⊑ b
    -> c ⊑ (a ⊓ b).
Proof.
  intros a b c. unfold lattice_le. intros.
  rewrite <- meet_assoc. now rewrite H0.
Qed.

Lemma finite_join_le {A : Type} `{BoundedLattice A} :
  forall (a : A) l, In a l -> a ⊑ finite_join l.
Proof.
  induction l.
  - simpl. intuition.
  - intros. simpl in H1.
    destruct H1.
    + subst. replace (a :: l) with ([a] ++ l) by auto.
      rewrite finite_join_app.
      unfold finite_join at 1. simpl.
      rewrite join_bottom_l. apply join_le.
    + replace (a0 :: l) with ([a0] ++ l) by auto.
      rewrite finite_join_app.
      unfold finite_join at 1. simpl.
      rewrite join_bottom_l. apply IHl in H1.
      transitivity (finite_join l). apply H1.
      rewrite join_comm. apply join_le.
Qed.


Lemma finite_meet_ge {A : Type} `{BoundedLattice A} :
  forall (a : A) l, In a l -> finite_meet l ⊑ a.
Proof.
  induction l.
  - simpl. intuition.
  - intros. simpl in H1.
    destruct H1.
    + subst. replace (a :: l) with ([a] ++ l) by auto.
      rewrite finite_meet_app.
      unfold finite_meet at 1. simpl.
      rewrite meet_top_l. apply meet_ge.
    + replace (a0 :: l) with ([a0] ++ l) by auto.
      rewrite finite_meet_app.
      unfold finite_meet at 1. simpl.
      rewrite meet_top_l. apply IHl in H1.
      transitivity (finite_meet l).
      rewrite meet_comm. apply meet_ge.
      apply H1.
Qed.

Lemma join_i_le {A : Type} `{BoundedLattice A} (start length : nat) (f : nat -> A)
  : forall a, start <= a -> a < start + length -> f a ⊑ join_i start length f.
Proof.
  intros. unfold join_i. unfold op_i.
  replace (finite_op A (map f (seq start length)))
    with (finite_join (map f (seq start length))) by auto.
  apply finite_join_le. apply in_map.
  apply in_seq. split. lia. lia.
Qed.

Lemma meet_i_ge {A : Type} `{BoundedLattice A} (start length : nat) (f : nat -> A)
  : forall a, start <= a -> a < start + length -> meet_i start length f ⊑ f a.
Proof.
  intros. unfold meet_i. unfold op_i.
  replace (finite_op A (map f (seq start length)))
    with (finite_meet (map f (seq start length))) by auto.
  apply finite_meet_ge. apply in_map.
  apply in_seq. split. lia. lia.
Qed.

Lemma join_b_le {A : Type} `{BoundedLattice A} (lo hi : nat) (f : nat -> A)
  : forall a, lo <= a -> a <= hi -> f a ⊑ join_b lo hi f.
Proof.
  intros. unfold join_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (join_i lo (S hi - lo) f) by auto.
  apply join_i_le. assumption. lia.
Qed.

Lemma meet_b_ge {A : Type} `{BoundedLattice A} (lo hi : nat) (f : nat -> A)
  : forall a, lo <= a -> a <= hi -> meet_b lo hi f ⊑ f a.
Proof.
  intros. unfold meet_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (meet_i lo (S hi - lo) f) by auto.
  apply meet_i_ge. assumption. lia.
Qed.

Lemma finite_join_sup {A : Type} `{BoundedLattice A} :
  forall (x : A) l,
    (forall a, In a l -> a ⊑ x)
    -> finite_join l ⊑ x.
Proof.
  induction l.
  - unfold finite_join. simpl. intros. apply bottom_le.
  - intros. replace (a :: l) with ([a] ++ l) by auto.
      rewrite finite_join_app.
      unfold finite_join at 1.
      simpl. rewrite join_bottom_l.
      simpl in H1. apply join_sup.
    + specialize (H1 a).
      auto.
    + apply IHl. auto.
Qed.

Lemma finite_meet_inf {A : Type} `{BoundedLattice A} :
  forall (x : A) l,
    (forall a, In a l -> x ⊑ a)
    -> x ⊑ finite_meet l.
Proof.
  induction l.
  - unfold finite_meet. simpl. intros. apply top_ge.
  - intros. replace (a :: l) with ([a] ++ l) by auto.
      rewrite finite_meet_app.
      unfold finite_meet at 1.
      simpl. rewrite meet_top_l.
      simpl in H1. apply meet_inf.
    + specialize (H1 a).
      auto.
    + apply IHl. auto.
Qed.

Lemma join_i_sup {A : Type} `{BoundedLattice A} (start length : nat) (f : nat -> A)
  : forall x, (forall a, start <= a -> a < start + length -> f a ⊑ x)
         -> join_i start length f ⊑ x.
Proof.
  intros. unfold join_i. unfold op_i.
  replace (finite_op A (map f (seq start length)))
    with (finite_join (map f (seq start length))) by auto.
  apply finite_join_sup.
  intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [a [Ha1 Ha2]].
  apply in_seq in Ha2. subst. apply H1. lia. lia.
Qed.

Lemma meet_i_inf {A : Type} `{BoundedLattice A} (start length : nat) (f : nat -> A)
  : forall x, (forall a, start <= a -> a < start + length -> x ⊑ f a)
         -> x ⊑ meet_i start length f.
Proof.
  intros. unfold meet_i. unfold op_i.
  replace (finite_op A (map f (seq start length)))
    with (finite_meet (map f (seq start length))) by auto.
  apply finite_meet_inf.
  intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [a [Ha1 Ha2]].
  apply in_seq in Ha2. subst. apply H1. lia. lia.
Qed.


Lemma join_b_sup {A : Type} `{BoundedLattice A} (lo hi : nat) (f : nat -> A)
  : forall x, (forall a, lo <= a -> a <= hi -> f a ⊑ x)
         -> join_b lo hi f ⊑ x.
Proof.
  intros. unfold join_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (join_i lo (S hi - lo) f) by auto.
  apply join_i_sup. intros. apply H1. lia. lia.
Qed.

Lemma meet_b_inf {A : Type} `{BoundedLattice A} (lo hi : nat) (f : nat -> A)
  : forall x, (forall a, lo <= a -> a <= hi -> x ⊑ f a)
         -> x ⊑ meet_b lo hi f.
Proof.
  intros. unfold meet_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (meet_i lo (S hi - lo) f) by auto.
  apply meet_i_inf. intros. apply H1. lia. lia.
Qed.

Lemma join_preserves_le {A : Type} `{Lattice A} :
  forall (a b c d : A), a ⊑ b -> c ⊑ d -> (a ⊔ c) ⊑ (b ⊔ d).
Proof.
  intros. apply join_sup.
  transitivity b. assumption.
  apply join_le. transitivity d.
  assumption. rewrite join_comm. apply join_le.
Qed.

Lemma meet_preserves_ge {A : Type} `{Lattice A} :
  forall (a b c d : A), a ⊑ b -> c ⊑ d -> (a ⊓ c) ⊑ (b ⊓ d).
Proof.
  intros. apply meet_inf.
  transitivity a. apply meet_ge.
  assumption. transitivity c.
  rewrite meet_comm. rewrite meet_ge.
  reflexivity. assumption.
Qed.


Lemma join_i_preserves_le {A : Type} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
  : (forall a, start <= a -> a < start + length -> f a ⊑ g a)
         -> join_i start length f ⊑ join_i start length g.
Proof.
  revert start. induction length.
  - intros. unfold join_i. unfold op_i.
    simpl. reflexivity.
  - intros. unfold join_i.
    repeat replace (S length) with (1 + length) by lia.
    repeat rewrite op_i_app.
    simpl. apply join_preserves_le.
    + unfold op_i. simpl. repeat rewrite finite_op_singleton.
      apply H1. lia. lia.
    + apply IHlength. intros. apply H1. lia. lia.
Qed.


Lemma meet_i_preserves_ge {A : Type} `{BoundedLattice A} (start length : nat) (f g : nat -> A)
  : (forall a, start <= a -> a < start + length -> f a ⊑ g a)
         -> meet_i start length f ⊑ meet_i start length g.
Proof.
  revert start. induction length.
  - intros. unfold meet_i. unfold op_i.
    simpl. reflexivity.
  - intros. unfold meet_i.
    repeat replace (S length) with (1 + length) by lia.
    repeat rewrite op_i_app.
    simpl. apply meet_preserves_ge.
    + unfold op_i. simpl. repeat rewrite finite_op_singleton.
      apply H1. lia. lia.
    + apply IHlength. intros. apply H1. lia. lia.
Qed.

Lemma join_b_preserves_le {A : Type} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
  : (forall a, lo <= a -> a <= hi -> f a ⊑ g a)
    -> join_b lo hi f ⊑ join_b lo hi g.
Proof.
  intros. unfold join_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (join_i lo (S hi - lo) f) by auto.
  replace (op_i A lo (S hi - lo) g)
    with (join_i lo (S hi - lo) g) by auto.
  apply join_i_preserves_le. intros. apply H1.
  lia. lia.
Qed.

Lemma meet_b_preserves_ge {A : Type} `{BoundedLattice A} (lo hi : nat) (f g : nat -> A)
  : (forall a, lo <= a -> a <= hi -> f a ⊑ g a)
    -> meet_b lo hi f ⊑ meet_b lo hi g.
Proof.
  intros. unfold meet_b. unfold op_b.
  replace (op_i A lo (S hi - lo) f)
    with (meet_i lo (S hi - lo) f) by auto.
  replace (op_i A lo (S hi - lo) g)
    with (meet_i lo (S hi - lo) g) by auto.
  apply meet_i_preserves_ge. intros. apply H1.
  lia. lia.
Qed.
