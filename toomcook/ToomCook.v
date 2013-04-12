Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq matrix.
Require Import path choice fintype tuple finset ssralg poly polydiv bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Open Scope ring_scope.

Section toomCook.

Variable R : comRingType.
Variable k : nat. (* Number of splits in Toom-n *)
Variable s : nat. (* Number of evaluation points *)
Variable evaluation_mat : 'M[{poly R}]_(s, k).
Variable interpolation_mat : 'M[{poly R}]_(s, s).
Implicit Types p q : {poly R}.

Definition exponent (k: nat) p q : nat :=
  maxn (divn (size p) k) (divn (size q) k) .+1.

(*
 * m is a k by 1 matrix
 * m(0, 0) = (p / x^0b) % x^b
 * m(1, 0) = (p / x^1b) % x^b
 * m(2, 0) = (p / x^2b) % x^b
 * m(3, 0) = (p / x^3b) % x^b
 * ...
*)

Definition split (e: nat) p : 'cV[{poly R}]_k :=
  \col_i rmodp (rdivp p 'X^(i * e)) 'X^e.

Definition evaluate (vec: 'cV[{poly R}]_k) : 'cV[{poly R}]_s :=
  (* TODO: vec must have correct order, in the haskell implementation we reverse the vector (list) *)
  mulmx evaluation_mat vec.

Definition interpolate (vec: 'cV[{poly R}]_s) : 'cV[{poly R}]_s :=
  mulmx interpolation_mat vec.

(* inversion of split *)
Definition recompose (e: nat) (vec: 'cV[{poly R}]_s) : {poly R} :=
  mulmx (\row_i 'X^(i * e)) vec ord0 ord0.

Fixpoint toom_cook_rec (n: nat) p q : {poly R} :=
  match n with
  | 0%N   => p * q
  | n'.+1 =>
    let e   := exponent k p q in
    let p'  := split e p in
    let q'  := split e q in
    let p'' := evaluate p' in
    let q'' := evaluate q' in
    let r   := \col_i (toom_cook_rec n' (p'' i ord0) (q'' i ord0)) in
    let r'  := interpolate r
     in recompose e r'
  end.

Definition toom_cook p q : {poly R} :=
  toom_cook_rec (maxn (size p) (size q)) p q.

End toomCook.