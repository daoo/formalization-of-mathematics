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
  reflexivity.
Qed.

Theorem plusn0: forall (n: nat),
  plus n O = n.
Proof.
  induction n as [ | n' IH ].
    unfold plus. reflexivity.
    simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem plusSn: forall (n m: nat),
  plus n (S m) = S (plus n m).
Proof.
  induction n as [ | n' IH ].
    (* n = 0 *)
    reflexivity.

    (* n = S n' *)
    intros m.
    simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem plusC: forall (n m: nat),
  plus n m = plus m n.
Proof.
  induction n as [ | n' IH ].
    (* n = 0 *)
    intros m.
    simpl.
    rewrite -> plusn0.
    reflexivity.

    (* n = S n' *)
    intros m.
    simpl.
    rewrite -> plusSn.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem plusA: forall (n m o: nat),
  plus n (plus m o) = plus (plus n m) o.
Proof.
  induction n as [ | n' IH ].
    (* n = 0 *)
    reflexivity.

    (* n = S n' *)
    intros m o.
    simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem mult0n: forall (n: nat),
  mult O n = O.
Proof.
  reflexivity.
Qed.

Theorem multn0: forall (n: nat),
  mult n O = O.
Proof.
  induction n as [ | n' IH ].
    reflexivity.
    simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem mult1n: forall (n: nat),
  mult (S O) n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plusn0.
  reflexivity.
Qed.

Theorem multn1: forall (n: nat),
  mult n (S O) = n.
Proof.
  induction n as [ | n' IH ].
    (* n = 0 *)
    reflexivity.

    (* n = S n' *)
    simpl.
    rewrite -> IH.
    reflexivity.
Qed.

Theorem plusSwap: forall (n m o: nat),
  plus n (plus m o) = plus m (plus n o).
Proof.
  intros n m o.
  rewrite plusC.
  rewrite <- plusA.  

Theorem multSn: forall (n m: nat),
  mult m (S n) = plus m (mult m n).
Proof.
  intros n m.
  generalize dependent n.
  induction m as [ | m' IH ].
    (* n = 0 *)
    reflexivity.

    (* n = S n' *)
    intros n.
    simpl.
    rewrite IH.
    rewrite plusA.

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
    