Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rework your last proof using the full syntax of ssreflect. *)

(* Solve the following equations. Search is your best friend. *)
Lemma ex5_arit1 n m : n + (m * n + 0) = n * m.+1.
Proof.
  by rewrite addn0 -add1n mulnDr muln1 mulnC.
Qed.

Lemma ex5_arit2 n m : n %/ 2 + m = (2 * m + n) %/ 2.
Proof.
  by rewrite mulnC divnMDl // addnC.
Qed.

Lemma ex5_arit3 n m p : 0 < p ->  p %| n -> n %/ p + m = (p * m + n) %/ p.
Proof.
  move=> Hp Hpn.
  rewrite divnDr //=.
  rewrite mulKn //=.
  by rewrite addnC.
Qed.

(* Prove this by induction. *)
Lemma size_iota_sumn l : sumn (map (addn 1) l) = size l + sumn l.
Proof.
  elim l => //= x xs IH.
  by rewrite !addSn [x + _]addnC addnA IH add0n addnC.
Qed.

(* Prove the following Theorem by induction. *)
Theorem ex5_gauss n : (n * n.-1) %/ 2 = sumn (iota 0 n).
Proof.
  elim n => //= n' IH.
    rewrite (iota_addl 1 0) add0n size_iota_sumn -IH{IH} size_iota.
    rewrite -{3}[n'](@mulnK _ 2) // -divnDl ?dvdn_mull //.
    by rewrite [_ * _.-1]mulnC !mulnS muln0 addn0 -addnA; case: n'.
Qed.

(* Advanced part *)

(* Read the documentation of the wlog tactic *)

(* Prove the following lemma without using dvdn_pexp2r following one the two informal
   proofs. The first one is more detailed, the second one is more challenging.
   If you want to try the second one, just skip ahead without reading the
   following informal proof. *)
Lemma ex5_dvdn : forall m n k, k > 0 -> (m ^ k %| n ^ k) -> (m %| n).
Proof.

(* Without loss of generality n is positive, since any number divides 0 *)

(* Given d := gcdn m n, n can be written as n' * d and m as m' * d *)




(* We also have d > 0 *)

(* We can now refine our assumption to m' ^ k %| n' ^ k
   since for b positive, a * b %| c * b -> a %| c     *)




(* We can also prove that (m' ^ k) and (n' ^ k) are coprime since
   the gcdn of m' and n' is 1, or equivalently (gcdn m' n') * d = d *)




(* From this coprimality and the refiner hypothesis follows that
   m' ^ k = 1 = gcdn (m' ^ k) (n' ^ k). Hint: gcdn a (a %% b) = gcdn a b *)



(* Since m'^k = 1 also m' = 1. Thus m = d and d %| n *)



Qed.

Lemma ex5_dvdn_advanced : forall m n k, k > 0 -> (m ^ k %| n ^ k) -> (m %| n).
Proof.
(* Without loss of generality we can assume (m ^ k) and (n ^ k) are coprime
   (i.e. dividing n and m by their gcdn).
   Since (m ^ k) also divides (n ^ k), (m ^ k) is 1, thus m is 1,
   thus it trivially divides n. *)










Qed.

