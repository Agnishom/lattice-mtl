Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.

Section last.

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

End last.
