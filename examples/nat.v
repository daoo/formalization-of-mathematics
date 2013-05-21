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