Require Import ssreflect ssrfun ssrbool eqtype.

Inductive nat: Set :=
  | O: nat
  | S: nat -> nat.

Fixpoint plus (n m: nat) :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m: nat) :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Theorem plus0n: forall (n: nat),
  plus O n = n.
Proof.
  done.
Qed.

Theorem plusn0: forall (n: nat),
  plus n O = n.
Proof.
  elim=> [ // | n' IH ] /=.
    by rewrite IH.
Qed.

Theorem plusSn: forall (n m: nat),
  plus n (S m) = S (plus n m).
Proof.
  elim=> [ // | n' IH m ] /=.
    by rewrite IH.
Qed.

Theorem plusC: forall (n m: nat),
  plus n m = plus m n.
Proof.
  elim=> [ m | n' IH m ] /=.
    by rewrite plusn0.
    by rewrite plusSn IH.
Qed.

Theorem plusA: forall (n m o: nat),
  plus n (plus m o) = plus (plus n m) o.
Proof.
  elim=> [ // | n' IH m o ] /=.
    by rewrite IH.
Qed.


Theorem mult0n: forall (n: nat),
  mult O n = O.
Proof.
  done.
Qed.

Theorem multn0: forall (n: nat),
  mult n O = O.
Proof.
  elim=> [ // | n' IH ] /=.
    by rewrite IH.
Qed.

Theorem mult1n: forall (n: nat),
  mult (S O) n = n.
Proof.
  by apply plusn0.
Qed.

Theorem multn1: forall (n: nat),
  mult n (S O) = n.
Proof.
  elim=> [ // | n' IH ] /=.
    by rewrite IH.
Qed.

Theorem plusSwap: forall (n m o: nat),
  plus n (plus m o) = plus m (plus n o).
Proof.
  move=> n m o.
  by rewrite plusA [X in plus X]plusC -plusA.
Qed.

Theorem multSn: forall (n m: nat),
  mult m (S n) = plus m (mult m n).
Proof.
  move=> n m.
  move: m.
  elim=> [ // | m' IH ].
    rewrite /=.
Qed.

Theorem multC: forall (n m: nat),
  mult n m = mult m n.
Proof.
  induction n as [ | n' IH ].
    (* n = 0 *)
    intros m.
    simpl.
    rewrite -> multn0.
    reflexivity.

    (* n = S n' *)
    intros m.
    simpl.
    