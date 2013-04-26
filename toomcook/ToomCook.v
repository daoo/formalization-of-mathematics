Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq matrix.
Require Import path choice fintype tuple finset ssralg poly polydiv bigop.
Require Import mxpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Open Scope ring_scope.

Section toomCook.

Variable R : comUnitRingType.
Implicit Types p q : {poly R}.

Variable number_points m : nat.
Definition d : nat := number_points.-1.
Variable inter_points : 'cV[R]_(d + 1).

Definition V_e : 'M[{poly R}]_(d+1, m) :=
  \matrix_(i < (d + 1), j < m) ((inter_points i ord0) %:P)^+j.

Definition V_I : 'M[R]_(d + 1) :=
  \matrix_(i < d + 1, j < d + 1) ((inter_points i ord0))^+j.

Definition V_I_inv : 'M[{poly R}]_(d + 1) :=
  \matrix_(i < d + 1, j < d + 1) ((invmx V_I) i j) %:P.

Definition exponent (m: nat) p q : nat :=
  maxn (divn (size p) m) (divn (size q) m) .+1.

Definition split (n b: nat) p : {poly {poly R}} :=
  \poly_(i < n) rmodp (rdivp p 'X^(i * b)) 'X^b.

Definition evaluate (u : {poly {poly R}}) : 'cV[{poly R}]_(d + 1) :=
  V_e *m (poly_rV u)^T.

Definition interpolate (u : 'cV[{poly R}]_(number_points)) : {poly {poly R}} :=
  rVpoly (V_I_inv *m u)^T.

Definition recompose (b: nat) (w: {poly {poly R}}) : {poly R} :=
  w.['X^b].

Fixpoint toom_cook_rec (n: nat) p q : {poly R} :=
  match n with
  | 0%N   => p * q
  | n'.+1 => if (size p <= 2) || (size q <= 2) then p * q else
    let b  := exponent m p q in
    let u  := split m b p in
    let v  := split m b q in
    let u' := evaluate u in
    let v' := evaluate v in
    let r  := \col_i toom_cook_rec n' (u' i ord0) (v' i ord0) in
    let r' := interpolate r
     in recompose b r'
  end.

Definition toom_cook p q : {poly R} :=
  toom_cook_rec (maxn (size p) (size q)) p q.

End toomCook.
