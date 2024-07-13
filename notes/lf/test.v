From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Require Import Cdcl.Itauto.
From Tactician Require Import Ltac1.
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
tauto. Show Proof.

Inductive list :=
| nil  : list
| cons : nat -> list -> list.


Notation "[]" := nil.
Notation "n :: ls" := (cons n ls).

Fixpoint concat ls1 ls2 :=
  match ls1 with
  | []      => ls2
  | x::ls1' => x::(concat ls1' ls2)
  end where "ls1 ++ ls2" := (concat ls1 ls2).

Lemma concat_nil_r : forall ls, ls ++ [] = ls.
Proof.
intros.
induction ls.
- simpl. reflexivity.
- simpl. f_equal. apply IHls.
Qed.


(*Lemma concat_assoc :
  forall ls ls2 ls3, (ls ++ ls2) ++ ls3 = ls ++ (ls2 ++ ls3).
Proof.
intros.
induction ls.
reflexivity.
simpl.
induction ls.
f_equal.
apply IHls.*)

Lemma concat_assoc1 :
  forall ls ls2 ls3, (ls ++ ls2) ++ ls3 = ls ++ (ls2 ++ ls3).
Proof.
synth with cache (only 1:
intros; only 1:
induction ls; only 1:
simpl; only 1: f_equal; only
1: simpl; only 1:
f_equal; only 1:
apply IHls).
Qed.


Lemma concat_assoc2 :
  forall ls ls2 ls3, (ls ++ ls2) ++ ls3 = ls ++ (ls2 ++ ls3).
Proof.
intros.
induction ls.
- simpl. reflexivity.
- simpl. rewrite IHls. reflexivity.
Qed.
