Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq matrix.
Require Import path choice fintype tuple finset ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.
Open Scope ring_scope.

Section toomCook.

Variable R : comRingType.
Implicit Types k : nat. (* Number of splits in Toom-n *)
Implicit Types s : nat. (* Number of evaluation points *)
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

Definition split k (e: nat) p : Vector {poly R} k :=
  matrix_of_fun k 1 (fun i _ => rmodp (rdivp p 'X^(i * e)) 'X^b).

Definition evaluate (mat: Matrix R s k) (vec: Vector {poly R} k) : Vector {poly R} s :=
  mulmx mat vec. (* TODO: vec must have correct order, in the haskell implementation we reverse the vector (list) *)

Definition interpolate (invmat: Matrix R s) (vec : Vector {poly R} k) : Vector {poly R} s :=
  mulmx invmat vec.

Definition pointwise k (n: nat) (A B: Vector {poly R} s) :=
  zipWith (toom_cook_rec n k) A B.

(* inversion of split *)
Definition recompose (e: nat) (A: Vector {poly R} s) :=
  snd (fold (fun (i, sum) p => (i + 1, sum + p * 'X^(i * e))) (0, 0) A).

Fixpoint toom_cook_rec (n k: nat) p q :=
  match n with
  | 0%N   => p * q
  | n'.+1 =>
    let b   := exponent k p q in
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
