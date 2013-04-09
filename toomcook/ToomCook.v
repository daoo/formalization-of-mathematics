Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq matrix.
Require Import path choice fintype tuple finset ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Open Scope ring_scope.

Section toomCook.

Variable R : comRingType.

Definition base_exponent (k: nat) (n m: {poly R}) : nat :=
  maxn (divn (size n) k) (divn (size m) k) .+1.

Fixpoint split_poly (k: nat) (n: {poly R}) :=
  match k with
  | O    => 0
  | S k' => rmodp n 'X^k' + split_poly k' (rdivp n 'X^k')
  end.
End toomCook.
