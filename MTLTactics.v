Require Import Coq.Lists.List.
Require Import Lia.
Require Import Omega.
Require Import Coq.Arith.PeanoNat.
From Hammer Require Import Hammer.

Import ListNotations.

(* List induction by length *)
Lemma list_length_ind {A : Type}: forall (P : list A -> Prop),
    (forall xs, (forall (l : list A), length l < length xs -> P l) -> P xs)
    -> forall xs, P xs.
Proof.
  intros P H.
  assert (forall xs l: list A, length l <= length xs -> P l) as H_ind.
  {
    induction xs; intros l Hlen; apply H; intros l0 H0.
    - inversion Hlen. omega.
    - apply IHxs. simpl in Hlen. omega.
  }
  intros xs.
  apply H_ind with (xs := xs).
  omega.
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
    rewrite app_length. simpl length at 3. omega.
Qed.


(* Same thing, for non-empty lists *)
Lemma list_r_ind_nonempty {A : Type} : forall (P : list A -> Prop),
                        (forall (x : A), P [x])
                        -> (forall x (xs : list A), (P xs -> P (xs ++ [x])))
                        -> forall xs, length xs > 0 -> P xs.
Proof.
  intros P H0 HI. induction xs using list_r_ind.
  - simpl. omega.
  - destruct xs.
    + simpl. auto.
    + intros. apply HI. apply IHxs. simpl. omega.
Qed.

Lemma last_nonempty {A : Type} : forall (x d : A) l,
    last (l ++ [x]) d = x.
Proof.
  induction l.
  - auto.
  - replace ((a :: l) ++ [x]) with (a :: (l ++ [x])) by auto.
    remember (l ++ [x]). destruct l0.
    + destruct l; inversion Heql0.
    + replace (last (a :: a0 :: l0)) with (last (a0 :: l0)) by auto.
      auto.
Qed.

Lemma last_app_nonempty {A : Type} : forall (x d : A) xs ys,
    last (ys ++ (xs ++ [x])) d = last (xs ++ [x]) d.
Proof.
  intros. rewrite app_assoc. rewrite last_nonempty. rewrite last_nonempty.
  auto.
Qed.

Lemma last_inversion {A : Type} : forall (x y : A) xs ys,
    xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
  intros. apply (f_equal (@rev A)) in H.
  repeat rewrite (rev_app_distr) in H.
  simpl in H. inversion H. apply (f_equal (@rev A)) in H2.
  repeat rewrite rev_involutive in H2.
  auto.
Qed.

Lemma removelast_nonempty {A : Type} : forall (x : A) xs,
    removelast (xs ++ [x]) = xs.
Proof.
  induction xs.
  - auto.
  - replace ((a :: xs) ++ [x]) with (a :: (xs ++ [x])) by reflexivity.
    simpl. rewrite IHxs. destruct (xs ++ [x]) eqn:E.
    + destruct xs; inversion E.
    + reflexivity.
Qed.

Lemma skipn_nonempty {A : Type} : forall (n : nat) (xs : list A),
    skipn n xs <> [] -> length xs >= n.
Proof.
  intros.
  destruct (skipn n xs) eqn:E; [Reconstr.scrush|].
  clear H.
  destruct PeanoNat.Nat.le_gt_cases with (n := n) (m := length xs).
  - auto.
  - pose proof (firstn_skipn n xs).
    apply (f_equal (@length A)) in H0.
    rewrite app_length in H0. rewrite firstn_length in H0.
    rewrite PeanoNat.Nat.min_r in H0 by lia. rewrite E in H0.
    simpl in H0. exfalso. lia.
Qed.

Lemma length_last {A : Type} (xs : list A) (x : A) :
  length (xs ++ [x]) = S (length xs).
Proof.
  induction xs.
  - auto.
  - replace ((a :: xs) ++ [x]) with (a :: (xs ++ [x])) by reflexivity.
    simpl. rewrite IHxs. reflexivity.
Qed.

(* Some theorems about tail *)
Lemma tl_length {A : Type} (xs : list A) :
  length (tail xs) = pred (length xs).
Proof.
  induction xs; auto.
Qed.

Lemma tl_app {A : Type} (xs ys : list A) :
  xs <> [] -> tail (xs ++ ys) = tail xs ++ ys.
Proof.
  intros. destruct xs; Reconstr.scrush.
Qed.

(* Taking the last n elements of a list *)

Definition lastn {A : Type} (n : nat) (xs : list A) := rev (firstn n (rev xs)).

Definition skiplastn {A : Type} (n : nat) (xs : list A) := rev (skipn n (rev xs)).

Lemma lastn_skiplastn {A : Type} (n : nat) (xs : list A) :
  skiplastn n xs ++ lastn n xs = xs.
Proof.
  unfold skiplastn. unfold lastn.
  rewrite <- rev_app_distr. rewrite firstn_skipn.
  now rewrite rev_involutive.
Qed.


Lemma lastn_all {A : Type} (l : list A) :
  lastn (length l) l = l.
Proof.
  unfold lastn. rewrite <- rev_length. rewrite firstn_all. rewrite rev_involutive.
  reflexivity.
Qed.

Lemma lastn_last {A : Type} (n : nat) (x : A) (xs : list A) :
  lastn (S n) (xs ++ [x]) = lastn n xs ++ [x].
Proof.
  unfold lastn. rewrite rev_app_distr.
  auto.
Qed.

Lemma lastn_le_length {A : Type} (n : nat) (xs : list A) :
  length (lastn n xs) <= n.
Proof.
  unfold lastn. rewrite rev_length. rewrite firstn_le_length.
  auto.
Qed.

Lemma lastn_0 {A : Type} (xs : list A) :
  lastn 0 xs = [].
Proof.
  unfold lastn. auto.
Qed.

Lemma lastn_nil {A : Type} (n : nat) :
  (@lastn A) n [] = [].
Proof.
  Reconstr.scrush.
Qed.

Lemma lastn_length {A : Type} (n : nat) (xs : list A) :
  length (lastn n xs) = Init.Nat.min n (length xs).
Proof.
  unfold lastn. rewrite rev_length. rewrite firstn_length.
  now rewrite rev_length.
Qed.

Lemma lastn_app {A : Type} (n : nat) (l1 l2 : list A) :
  lastn n (l1 ++ l2) = (lastn (n - length l2) l1) ++ (lastn n l2).
Proof.
  unfold lastn at 1. rewrite rev_app_distr. rewrite firstn_app.
  rewrite rev_app_distr. Reconstr.scrush.
Qed.

Lemma lastn_app_2 {A : Type} (n : nat) (l1 l2 : list A) :
  lastn (length l2 + n) (l1 ++ l2) = (lastn n l1) ++ l2.
Proof.
  unfold lastn at 1. rewrite rev_app_distr. rewrite <- rev_length.
  rewrite firstn_app_2. rewrite rev_app_distr. Reconstr.scrush.
Qed.

Lemma lastn_all2 {A : Type} (n : nat) (xs : list A) :
  n >= length xs
  -> lastn n xs = xs.
Proof.
  unfold lastn. intros. rewrite firstn_all2. now rewrite rev_involutive.
  rewrite rev_length; lia.
Qed.

Lemma lastn_tail {A : Type} (n : nat) (xs : list A):
  n < length xs
  -> lastn n (tail xs) = lastn n xs.
Proof.
Admitted.

Lemma tail_lastn {A : Type} (n : nat) (xs : list A):
  n < length xs
  -> tl (lastn (S n) xs) = lastn n xs.
Admitted.

Lemma last_firstn {A : Type} (n : nat) (xs ys : list A) (d : A):
  length xs > n
  -> last (firstn (S n) xs) d = last (firstn (S (length ys + n)) (ys ++ xs)) d.
Proof.
  intros.
  (* Step 1: last (firstn (S n) xs) = last (ys ++ (firstn (S n) xs)) *)
  remember (firstn (S n) xs) as blah.
  destruct blah using list_r_ind.
  { apply f_equal with (f := @length A) in Heqblah.
    rewrite firstn_length in Heqblah.
    replace (Init.Nat.min (S n) (length xs)) with (S n) in Heqblah by lia.
    inversion Heqblah.
  }
  (* Now we know that this expression is nonempty. *)
  clear IHblah.
  rewrite <- last_app_nonempty with (ys0 := ys).
  rewrite Heqblah. rewrite <- firstn_app_2.
  f_equal. replace ((length ys) + S n) with (S (length ys + n)) by lia. auto.
Qed.

Lemma last_firstn_lastn {A : Type} (m n : nat) (xs : list A) (d : A):
  length xs >= n ->
  n > m ->
  last (firstn (S m) (lastn n xs)) d = last (firstn (S (length xs - n + m)) xs) d.
Proof.
  intros.
  assert (length (lastn n xs) = n).
  { rewrite lastn_length. lia. }
  rewrite last_firstn with (ys := (skiplastn n xs)) by lia.
  rewrite lastn_skiplastn.
  f_equal; f_equal; f_equal; f_equal.
  rewrite <- lastn_skiplastn with (xs0 := xs) (n0 := n) at 2.
  rewrite app_length. lia.
Qed.

(* Some theorems that connect existsb to exists *)

Lemma existsb_exists2' {A : Type} (xs : list A) (f : A -> bool):
  existsb f xs = true
  -> exists n, forall d, f (last (firstn (S n) xs) d) = true.
Proof.
  intros. induction xs.
  - inversion H.
  - replace (a :: xs) with ([a] ++ xs) in H by auto.
    rewrite existsb_app in H. apply Bool.orb_prop in H as [].
    + exists 0. Reconstr.scrush.
    + apply IHxs in H as []. exists (S x). Reconstr.scrush.
Qed.

Lemma existsb_exists2'' {A : Type} (xs : list A) (f : A -> bool):
  existsb f xs = true
  -> exists n, n < length xs /\ forall d, f (last (firstn (S n) xs) d) = true.
Proof.
  intros. destruct xs. inversion H.
  apply existsb_exists2' in H as [n'].
  destruct (Nat.lt_ge_cases n' (length (a :: xs))).
  - Reconstr.scrush.
  - exists (length xs). split. simpl; lia.
    replace (S (length xs)) with (Init.Nat.min (S n') (length (a :: xs))).
    rewrite <- firstn_firstn. rewrite firstn_all. auto. simpl in *. lia.
Qed.


Lemma existsb_exists2 {A : Type} (xs : list A) (x : A) (f : A -> bool):
  existsb f (xs ++ [x]) = true -> exists n, f (last (firstn (S n) (xs ++ [x])) x) = true.
Proof.
  pose proof existsb_exists2' (xs ++ [x]).
  intros. apply H in H0.
  Reconstr.scrush.
Qed.

Lemma exists2_existsb {A : Type} (xs : list A) (x : A) (f : A -> bool):
  (exists n, f (last (firstn n (xs ++ [x])) x) = true)
                      -> existsb f (xs ++ [x]) = true.
Proof.
  generalize dependent x. induction xs.
  - intros x [n]. simpl in H. Reconstr.ryelles4 Reconstr.Empty Reconstr.Empty.
  - intros x [m]. destruct m.
    + simpl in H. rewrite existsb_app. simpl. rewrite H. simpl. rewrite Bool.orb_true_r. auto.
    + destruct m.
      ++ simpl in *. rewrite H. auto.
      ++ simpl app. simpl existsb. rewrite IHxs. now rewrite Bool.orb_true_r.
         exists (S m). Reconstr.scrush.
Qed.

(* Similar theorems for forallb *)
Lemma forallb_forall2' {A : Type} (xs : list A) (x : A) (f : A -> bool):
  forallb f (xs ++ [x]) = true
  -> forall n, f (last (firstn (S n) (xs ++ [x])) x) = true.
Proof.
  intros. generalize dependent x. generalize dependent n. induction xs.
  - simpl app in *. destruct n. Reconstr.scrush. simpl. Reconstr.scrush.
  - simpl app. intros. replace (a :: (xs ++ [x])) with ([a] ++ (xs ++ [x])) in * by auto.
    rewrite forallb_app in H. rewrite Bool.andb_true_iff in H. destruct H.
    destruct n.
    + Reconstr.scrush.
    + apply IHxs with (n := n) in H0. Reconstr.scrush.
Qed.

Lemma forall2_forallb {A : Type} (xs : list A) (x : A) (f : A -> bool):
  (forall n, f (last (firstn (S n) (xs ++ [x])) x) = true)
  -> forallb f (xs ++ [x]) = true.
Proof.
  intros. generalize dependent x.
  induction xs.
  - simpl app. intros. specialize (H 0). Reconstr.scrush.
  - intros. simpl app in *.
    replace (a :: (xs ++ [x])) with ([a] ++ (xs ++ [x])) in * by auto.
    rewrite forallb_app. rewrite Bool.andb_true_iff. split.
    + specialize (H 0). Reconstr.scrush.
    + apply IHxs. intros. specialize (H (S n)). Reconstr.scrush.
Qed.

Lemma forall2_forallb' {A : Type} (xs : list A) (x : A) (f : A -> bool):
  (forall n, n < length (xs ++ [x]) -> f (last (firstn (S n) (xs ++ [x])) x) = true)
  -> forallb f (xs ++ [x]) = true.
Proof.
  intros. apply forall2_forallb. intros.
  destruct (Nat.lt_ge_cases n (length (xs ++ [x]))).
  auto.
  rewrite <- firstn_all with (l := (xs ++ [x])).
  rewrite firstn_firstn.
  replace (Init.Nat.min (S n) (length (xs ++ [x])))
    with (length (xs ++ [x])) by lia.
  rewrite app_length. simpl. replace (length xs + 1) with (S (length xs)) by lia.
  apply H. rewrite app_length. simpl. lia.
Qed. 

Lemma rev'_rev {A : Type}:
  forall xs, rev' xs = @rev A xs.
Proof.
  intros; now rewrite rev_alt.
Qed.

(* Given a conjunction A /\ B, this lets you assume A when proving B *)
Ltac split_rem_left h :=
  match goal with
  | |- ?A /\ ?B =>
    assert A as h ; [
    | split ; [
        exact h
      |]
    ]
  end.

(* Similar, but on the other side. *)

Ltac split_rem_right h :=
  match goal with
  | |- ?A /\ ?B =>
    assert B as h ; [
    | split ; [
        exact h
      |]
    ]
  end.

(* Destructing functions with pairs *)
(* Does not seem to work. I am not sure why *)
Ltac introsP H a b :=
  match goal with
  | [ H : (forall x y, ?f ?t = (x, y) -> ?X) |- _ ] =>
    destruct (f t) as [a b] eqn:XX; specialize (H x y XX)
  | [ H : (forall x y, (x, y) = ?f ?t -> ?X) |- _ ] =>
    destruct (f t) as [a b] eqn:XX; specialize (H x y XX)
  end.

(* Prefixes *)

Fixpoint scan_left {A B : Type} (op : A -> B -> A) (l : list B) (init : A) : list A :=
  match l with
  | [] => [init]
  | (x :: xs) => init :: scan_left op xs (op init x)
  end.

Lemma scan_left_length {A B : Type}: forall (op : A -> B -> A) init (l : list B),
    length (scan_left op l init) = S (length l).
Proof.
  intros. generalize dependent init.
  induction l.
  + auto.
  + simpl. intros. now rewrite IHl.
Qed.

Lemma scan_left_app_last {A B : Type} (op : A -> B -> A) (xs : list B) (init : A) (x : B) :
  scan_left op (xs ++ [x]) init = (scan_left op xs init) ++ [(fold_left op (xs ++ [x]) init)].
Proof.
  generalize dependent init. induction xs.
  - reflexivity.
  - intros. simpl. now rewrite IHxs.
Qed.


Lemma scan_left_app {A B : Type} (op : A -> B -> A) (xs ys: list B) (y : B) (init : A) :
  scan_left op ((xs ++ [y]) ++ ys) init =
  (scan_left op xs init) ++ scan_left op ys (fold_left op (xs ++ [y]) init).
Proof.
  generalize dependent xs. generalize dependent init. induction ys using list_r_ind.
  - intros. rewrite app_nil_r. simpl. now rewrite scan_left_app_last.
  - intros. rewrite app_assoc. rewrite scan_left_app_last.
    rewrite IHys. rewrite scan_left_app_last. rewrite app_assoc.
    now repeat rewrite fold_left_app.
Qed.

Lemma scan_left_last {A B : Type} (op : A -> B -> A) (xs : list B) (init : A) :
  forall d, last (scan_left op xs init) d = fold_left op xs init.
Proof.
  induction xs using list_r_ind.
  - Reconstr.scrush.
  - intros. rewrite scan_left_app_last. simpl.
    rewrite last_nonempty. now rewrite fold_left_app.
Qed.

Lemma scan_left_firstn {A B : Type} (op : A -> B -> A) (xs : list B) (init : A) (n : nat) :
  scan_left op (firstn n xs) init = firstn (S n) (scan_left op xs init).
Proof.
  rewrite <- firstn_skipn with (l := xs) (n := n) at 2.
  destruct (skipn n xs) eqn:E.
  - rewrite app_nil_r. rewrite firstn_all2 with (n := S n). reflexivity.
    rewrite scan_left_length. rewrite firstn_length. lia.
  - replace (b :: l) with ([b] ++ l) by auto. rewrite app_assoc.
    rewrite scan_left_app. rewrite firstn_app.
    assert ((S n) = length (scan_left op (firstn n xs) init)).
    { rewrite scan_left_length.
      pose proof (skipn_nonempty n xs).
      specialize (H ltac:(Reconstr.scrush)).
      rewrite firstn_length.
      rewrite PeanoNat.Nat.min_l by lia. auto.
    }
    rewrite <- H. replace (S n - S n) with 0 by lia.
    rewrite firstn_O. rewrite app_nil_r. rewrite firstn_all2 with (n := S n).
    reflexivity. lia.
Qed.

Lemma scan_left_firstn_last {A B : Type} (op : A -> B -> A) (xs : list B) (init : A) (n : nat) :
  forall d,
       last (firstn (S n) (scan_left op xs init)) d = fold_left op (firstn n xs) init.
Proof.
  pose proof (@scan_left_firstn A B).
  pose proof (@scan_left_last A B).
  Reconstr.scrush.
Qed.

Definition prefixes {A : Type} (xs : list A) : list (list A) :=
  scan_left (fun xs x => xs ++ [x]) xs [].

Lemma prefixes_app_last {A : Type} (xs : list A) (x : A) :
  prefixes (xs ++ [x]) = prefixes xs ++ [(xs ++ [x])].
Proof.
  unfold prefixes. rewrite scan_left_app_last. simpl.
  assert (forall xs, fold_left (fun (xs0 : list A) (x0 : A) => xs0 ++ [x0]) xs [] = xs).
  { induction xs0 using list_r_ind. auto. rewrite fold_left_app.
    rewrite IHxs0. reflexivity. }
  now rewrite H.
Qed.

Lemma scan_left_prefixes {A B : Type} (op : A -> B -> A) (xs : list B) (init : A) :
  scan_left op xs init = map (fun l => fold_left op l init) (prefixes xs).
Proof.
  generalize dependent init. induction xs using list_r_ind.
  - auto.
  - intros. rewrite scan_left_app_last. rewrite prefixes_app_last.
    rewrite map_app. rewrite IHxs. simpl.
    now rewrite fold_left_app.
Qed.

(* range from lo to hi *)

Lemma seq_app : forall len1 len2 start,
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
    induction len1 as [|len1' IHlen]; intros; simpl in *.
    - now rewrite Nat.add_0_r.
    - now rewrite Nat.add_succ_r, IHlen.
Qed.

Lemma map_seq_last {B : Type} : forall i n (f : nat -> B),
    map f (seq i (S n)) = map f (seq i n) ++ [f (i + n)].
Proof.
  intros. replace (S n) with (n + 1) by lia. rewrite seq_app.
  rewrite map_app. auto.
Qed.

(* eta converting a list *)

Lemma list_eta {A : Type} (xs : list A) (d : A) :
  xs = map (fun i => last (firstn (S i) xs) d) (seq 0 (length xs)).
Proof.
  induction xs using list_r_ind.
  - auto.
  - rewrite app_length. simpl length at 2. rewrite seq_app.
    rewrite map_app. simpl seq at 2.
    replace ( map (fun i : nat => last (firstn (S i) (xs ++ [x])) d) [length xs])
      with [(last (firstn (S (length xs)) (xs ++ [x])) d)].
    rewrite map_ext_in with
        (f :=  (fun i : nat => last (firstn (S i) (xs ++ [x])) d))
        (g :=  (fun i : nat => last (firstn (S i) (xs )) d)).
    rewrite <- IHxs.
    replace (S (length xs)) with (length xs + 1) by lia.
    replace (length xs + 1) with (length xs + length [x]) by auto.
    replace (length xs + length [x]) with (length (xs ++ [x])) by now rewrite app_length.
    rewrite firstn_all. now rewrite last_nonempty.
    intros. rewrite in_seq in H. rewrite firstn_app.
    replace (S a - length xs) with 0 by lia. simpl firstn at 2.
    now rewrite app_nil_r.
    auto.
Qed.

(* index shifting *)

Lemma index_shift {A : Type} (f : nat -> A) (h n : nat):
  map (fun i => f (h + i)) (seq 0 n) = map f (seq h n).
Proof.
  induction n.
  - auto.
  - replace (S n) with (n + 1) by lia. repeat rewrite seq_app.
    repeat rewrite map_app. rewrite IHn. simpl.
    reflexivity.
Qed.

(* zip/unzip *)

Definition unzip_fst {A B : Type} (l : list (A * B)) : list A := map fst l.

Definition unzip_snd {A B : Type} (l : list (A * B)) : list B := map snd l.

Lemma unzip_fst_length {A B : Type}:
  forall (l : list (A * B)), length (unzip_fst l) = length l.
Proof.
  pose proof map_length. Reconstr.scrush.
Qed.

Lemma unzip_snd_length {A B : Type}:
  forall (l : list (A * B)), length (unzip_snd l) = length l.
Proof.
  pose proof map_length. Reconstr.scrush.
Qed.

Lemma unzip_fst_snd_length {A B : Type}:
  forall (l : list (A * B)), length (unzip_snd l) = length (unzip_fst l).
Proof.
  Reconstr.reasy (@unzip_fst_length, @unzip_snd_length) Reconstr.Empty.
Qed.

Lemma repeat_map {A B : Type} :
  forall (f : A -> B) (a : A) (n : nat), map f (repeat a n) = (repeat (f a) n).
Proof.
  intros. induction n; Reconstr.scrush.
Qed.

Lemma unzip_fst_repeat {A B : Type} :
  forall n (a : A) (b : B), unzip_fst (repeat (a, b) n) = repeat a n.
Proof.
  intros. unfold unzip_fst. now rewrite repeat_map.
Qed.

Lemma unzip_snd_repeat {A B : Type} :
  forall n (a : A) (b : B), unzip_snd (repeat (a, b) n) = repeat b n.
Proof.
  intros. unfold unzip_snd. now rewrite repeat_map.
Qed.

Lemma firstn_repeat {A : Type} :
  forall (a : A) i j, firstn i (repeat a j) = repeat a (min i j).
Proof.
  
Admitted.

Lemma lastn_repeat {A : Type} :
  forall (a : A) i j, lastn i (repeat a j) = repeat a (min i j).
Proof.
Admitted.

(* connecting hd_lastn and last_firstn *)

Lemma firstn_lastn {A : Type} (n : nat) (xs : list A) :
  n <= length xs -> xs = firstn n xs ++ lastn (length xs - n) xs.
Proof.
  intros.
  rewrite <- firstn_skipn with (n := n) at 1. f_equal.
  unfold lastn. rewrite <- firstn_skipn with (n := n) (l := xs) at 3.
  rewrite rev_app_distr. rewrite firstn_app.
  rewrite rev_length. pose proof (firstn_skipn n xs).
  eapply f_equal in H0. rewrite app_length in H0. rewrite firstn_length in H0.
  replace (Init.Nat.min n (length xs)) with n in H0 by lia.
  replace (length xs - n - length (skipn n xs)) with 0 by lia.
  rewrite firstn_all2. simpl. rewrite app_nil_r. now rewrite rev_involutive.
  rewrite rev_length. lia.
Qed.

Lemma lastn_lastn
  : forall (A : Type) (l : list A) (i j : nat), lastn i (lastn j l) = lastn (Init.Nat.min i j) l.
Proof.
  intros. unfold lastn. rewrite rev_involutive.
  now rewrite firstn_firstn. 
Qed.

Lemma hd_lastn_last_firstn {A : Type} (xs : list A) (n : nat) :
  S n <= length xs
  -> forall d, hd d (lastn (S n) xs) =
         last (firstn (S (length xs - S n)) xs) d.
Proof.
  intros.
  assert ((S (length xs - S n)) <= length xs) by lia.
  pose proof (firstn_lastn (S (length xs - S n)) xs H0).
  replace (length xs - S (length xs - S n)) with n in H1 by lia.
  remember (firstn (S (length xs - S n)) xs).
  destruct l using list_r_ind.
  - eapply f_equal in Heql. rewrite firstn_length in Heql.
    simpl length in Heql. lia.
  - clear IHl.
    rewrite H1. rewrite lastn_app. rewrite lastn_all2 with (n0 := S n).
    rewrite lastn_length.
    replace (S n - Init.Nat.min n (length xs)) with 1 by lia.
    unfold lastn at 1. rewrite rev_app_distr. simpl.
    now rewrite last_nonempty.
    rewrite lastn_length. lia.
Qed.

(* relating map and firstn or lastn *)

Lemma map_firstn {A B : Type}:
  forall (xs : list A) n (f : A -> B), firstn n (map f xs) = map f (firstn n xs).
Proof.
  intros. generalize dependent xs. induction n; sauto.
Qed.

Lemma map_lastn {A B : Type}:
  forall (xs : list A) n (f : A -> B), lastn n (map f xs) = map f (lastn n xs).
Proof.
  unfold lastn. intros.
  sauto using (map_rev, @map_firstn A B).
Qed.

(* A tail-recursive version of repeat *)

Lemma repeat_snoc_cons {A : Type} (x : A) (n : nat) :
  repeat x n ++ [x] = x :: repeat x n.
Proof.
  induction n; Reconstr.scrush.
Qed.

Fixpoint repeatAux {A : Type} (x : A) (n : nat) (acc : list A) :=
  match n with
  | O => acc
  | S k => repeatAux x k (x :: acc)
  end.

Definition repeat' {A : Type} (x : A) (n : nat) :=
  repeatAux x n [].

Lemma repeatAux_correctness {A : Type} (x : A) (xs : list A) (n : nat) :
  repeatAux x n xs = (repeat x n) ++ xs.
Proof.
  generalize dependent xs. induction n; [Reconstr.scrush | ].
  intros. simpl repeat. simpl repeatAux. rewrite IHn.
  rewrite <- repeat_snoc_cons. Reconstr.scrush.
Qed.

Lemma repeat_repeat' {A : Type} (x : A) (n : nat) :
  repeat' x n = (repeat x n).
Proof.
  unfold repeat'. sauto using (@repeatAux_correctness A).
Qed.

Lemma tl_map :
  forall {A B : Type} (f : A -> B) xs, map f (tl xs) = tl (map f xs).
Proof.
  destruct xs; auto.
Qed.
