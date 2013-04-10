Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq matrix.
Require Import path choice fintype tuple finset ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Open Scope ring_scope.

Section toomCook.

Variable R : comRingType.
Implicit Types p q : {poly R}.

Definition base_exponent (k: nat) p q : nat :=
  maxn (divn (size p) k) (divn (size q) k) .+1.

Definition split {m} (k : nat) (p : poly R) (M : 'M[poly R]_(m, 1)) : 'M[poly R]_(m+1, 1) :=
  match k with
  | O    => herp
  | S k' => derp
  end.

Definition evaluate {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  mulmx A B.

Definition interpolate {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  mulmx A B.

Definition pointwise := herp.

Definition recompose := derp.

Fixpoint toom_cook_rec (n k: nat) p q :=
  match n with
  | 0%N   => p * q
  | n'.+1 =>
    let b   := base_exponent k p q in
    let p'  := split k b p in
    let q'  := split k b q in
    let p'' := evaluate p' in
    let q'' := evaluate q' in
    let r   := pointwise toom_cook_rec n' k p'' q'' in
    let r'  := interpolate r
     in recompose b r'
  end.

Definition toom_cook (k: nat) p q :=
  toom_cook_rec (maxnn (size p) (size q)) k p q.

End toomCook.
