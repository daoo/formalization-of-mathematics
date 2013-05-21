Require Import ssreflect ssrfun ssrbool eqtype.

Inductive nat: Set :=
  | O: nat
  | S: nat -> nat.

Fixpoint plus (n m: nat) :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
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