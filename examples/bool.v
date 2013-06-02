Inductive bool: Set :=
  | true: bool
  | false: bool.

Definition and (a b: bool) : bool :=
  match a, b with
  | true, true => true
  | _   , _    => false
  end.

Definition or (a b: bool) : bool :=
  match a, b with
  | false, false => false
  | _    , _     => true
  end.

Definition not (a: bool) : bool :=
  match a with
  | true  => false
  | false => true
  end.

Theorem notK: forall (a: bool),
  not (not a) = a.
Proof.
  destruct a; reflexivity.
Qed.

Theorem deMorgan1: forall (a b: bool),
  not (and a b) = or (not a) (not b).
Proof.
  destruct a; destruct b; reflexivity.
Qed.

Theorem deMorgan2: forall (a b: bool),
  not (or a b) = and (not a) (not b).
Proof.
  destruct a; destruct b; reflexivity.
Qed.

Theorem complementation1: forall (a: bool),
  and (not a) a = false.
Proof.
  destruct a; reflexivity.
Qed.

Theorem complementation2: forall (a: bool),
  or (not a) a = true.
Proof.
  destruct a; reflexivity.
Qed.