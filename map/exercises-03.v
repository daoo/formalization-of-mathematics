Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finset zmodp matrix bigop ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.

Section Exercise.

(*********************************************************************)
(* Define the following matrices over an arbitrary ring R            *)
(* - A row matrice Rn of length n that has a 1 as its last element   *)
(*   all the other being 0s, for n = 4 this gives [0 0 0 1]          *)
(* - A column matrice Cn of length n that has a 1 as its last element*)
(*   all the other being 0s, for n = 4 this gives [0                 *)
(*                                                 0                 *)
(*                                                 0                 *)
(*                                                 1]                *)
(*                                                                   *)
(* - A square matrice Xn of length n that has 1s on the main diagonal*)
(*   and the right and bottom borders all the others being 0s,       *)
(*   for n = 4 this gives                         [1 0 0 1           *)
(*                                                 0 1 0 1           *)
(*                                                 0 0 1 1           *)
(*                                                 1 1 1 1]          *)
(*                                                                   *)
(* Hints : use the \row_ (_ < _) _, \col_ (_ < _) _,                 *)
(*                 \matrix_ (_ < _) (_ < _)                          *)
(* For Xn, give a direct definition and a recursive one using blocks *)
(* (for advanced users prove the equality of the two definitions)    *)
(* Hints : use block_mx the for definition                           *)
(*         and the theorems mxE split1 unliftP for the proof         *)
(*********************************************************************)

Variable R : ringType.


Check (fun f : nat -> R => \row_ (i < 3) f i).
Check (fun f : nat -> R => \col_ (i < 3) f i).
Check (fun f : nat -> R => \matrix_ (i < 3, j < 3) f (i + j)).

Check (@block_mx R).

Check (@mxE R).

Check split1.

Check unliftP.

(*********************************************************************)
(*                                                                   *)
(* Given an arbitrary matrix A, write a function msum that sums of   *)
(* elements of A,  show that                                         *)
(* - the msum of the sum of two matrices A B is the sum of msum of A *)
(*    and the msum of B                                              *)
(* - the msums of a matrix and of its  transpose are equal           *)
(*                                                                   *)
(* Hints use the bigop operation \sum_(_ < _) _ for the definition   *)
(*       use the theorems for the proof mxE big_split eq_bigr        *)
(*********************************************************************)

Check (fun f : nat -> R => \sum_ (i < 3) f i).

Check big_split.

Check eq_bigr.

End Exercise.