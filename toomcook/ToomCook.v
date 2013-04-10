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

Fixpoint split (k: nat) (n: {poly R}) : seq {poly R} :=
  match k with
  | O    => nil
  | S k' => rmodp n 'X^k' :: split k' (rdivp n 'X^k')
  end.
End toomCook.
