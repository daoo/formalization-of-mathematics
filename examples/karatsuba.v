Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finset ssralg poly polydiv.

(* Standard stuff to make Coq behave the way SSReflect wants *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensives.

(* Import necessary theory about rings and polynomial division *)
Import GRing.Theory Pdiv.Ring Pdiv.CommonRing Pdiv.RingMonic.

(* Open the correct scope so that 0, 1, + and * are interpreted correctly *)
Open Scope ring_scope.

(* Open a section *)
Section karatsuba.

(* Let R be a commutative ring, i.e. a structure where we have 0, 1, + and *
   that behave the way we expect and where multiplication is commutative *)
Variable R : comRingType.

(* Make p and q always have type polynomial over R so that we don't have to
   write it everywhere *)
Implicit Types p q : {poly R}.

(* Splitting of polynomials defined using polynomial division.
   rdivp is division and rmodp is modulus. *)
Definition split_poly n p := (rdivp p 'X^n, rmodp p 'X^n).

(* Main property of split_poly *)
Lemma split_polyP n p : p = (split_poly n p).1 * 'X^n + (split_poly n p).2.
Proof.
  by rewrite /split_poly -rdivp_eq // monicE lead_coefXn.
Qed.

Lemma div_mod_poly n p : p = rdivp p 'X^n * 'X^n + rmodp p 'X^n.
Proof.
  by apply rdivp_eq; rewrite monicE lead_coefXn.
Qed.

(* Recursive part of karatsuba multiplication. Parametrize by a natural number
   to make Coq realize that the code always terminate (this means that induction
   should be done on n in the correctness proof). *)
Fixpoint karatsuba_rec (n : nat) p q := match n with
  | 0%N   => p * q
  | n'.+1 =>
      let sp := size p in let sq := size q in
      if (sp <= 2) || (sq <= 2) then p * q else
        let m       := minn sp./2 sq./2 in
        let (p1,p2) := split_poly m p in
        let (q1,q2) := split_poly m q in
        let p1q1    := karatsuba_rec n' p1 q1 in
        let p2q2    := karatsuba_rec n' p2 q2 in
        let p12     := p1 + p2 in
        let q12     := q1 + q2 in
        let p12q12  := karatsuba_rec n' p12 q12 in
        p1q1 * 'X^(2 * m) + (p12q12 - p1q1 - p2q2) * 'X^m + p2q2
  end.

(* The final karatsuba function calls the recursive part with a "large enough
   number", i.e. the maximum of the degrees of the polynomials *)
Definition karatsuba p q := karatsuba_rec (maxn (size p) (size q)) p q.

Lemma karatsuba_split : forall p q,
  rdivp (R:=R) p 'X^(minn (size p)./2 (size q)./2) *
  rdivp (R:=R) q 'X^(minn (size p)./2 (size q)./2) *
  'X^(2 * minn (size p)./2 (size q)./2) +
  ((rdivp (R:=R) p 'X^(minn (size p)./2 (size q)./2) +
    rmodp (R:=R) p 'X^(minn (size p)./2 (size q)./2)) *
  (rdivp (R:=R) q 'X^(minn (size p)./2 (size q)./2) +
    rmodp (R:=R) q 'X^(minn (size p)./2 (size q)./2)) -
  rdivp (R:=R) p 'X^(minn (size p)./2 (size q)./2) *
  rdivp (R:=R) q 'X^(minn (size p)./2 (size q)./2) -
  rmodp (R:=R) p 'X^(minn (size p)./2 (size q)./2) *
  rmodp (R:=R) q 'X^(minn (size p)./2 (size q)./2)) *
  'X^(minn (size p)./2 (size q)./2) +
  rmodp (R:=R) p 'X^(minn (size p)./2 (size q)./2) *
  rmodp (R:=R) q 'X^(minn (size p)./2 (size q)./2) = p * q.
Proof.
  move=> p q.
  set d := minn (size p)./2 (size q)./2.

  set p1 := rdivp (R:=R) p 'X^d.
  set p2 := rmodp (R:=R) p 'X^d.
  set q1 := rdivp (R:=R) q 'X^d.
  set q2 := rmodp (R:=R) q 'X^d.

  have -> : ((p1 + p2) * (q1 + q2) = p1 * q1 + p1 * q2 + (p2 * q1 + p2 * q2))
    by rewrite mulrDl ?mulrDr.

  rewrite -?addrA.

  have -> : (p2 * q2 + (- (p1 * q1) - p2 * q2) = - (p1 * q1))
    by rewrite addrC -?addrA addNr addr0.

  have -> : (p1 * q1 + (p1 * q2 + (p2 * q1 - p1 * q1)) = p1 * q2 + p2 * q1)
    by rewrite addrC -?addrA addNr addr0 addrC.

  have -> : (p1 * q1 * 'X^(2 * d) = p1 * q1 * 'X^d * 'X^d)
    by rewrite mul2n -addnn exprD mulrA.

  rewrite ?addrA -mulrDl ?addrA.

  have extractp: (forall (a b c : {poly R}), a * b * 'X^d + a * c = a * (b * 'X^d + c)).
    by move=> a b c; rewrite -mulrA -mulrDr.
  rewrite extractp.

  rewrite -div_mod_poly.

  rewrite mulrDl -addrA extractp -div_mod_poly.
  by rewrite -mulrA (mulrC q 'X^d) mulrA -mulrDl -div_mod_poly.
Qed.

(* Correctness of the recursive part *)
Lemma karatsuba_recP : forall n p q, karatsuba_rec n p q = p * q.
Proof.
(* Some hints:

- The proof should be by induction on n.
- To handle the "if-then-else" do "case: ifP".
- It might be very useful to use the "set" tactic in order to make the goal
  more readable (i.e. to hide all rdivp and rmodp).
- As usual Search and looking in the files (ssralg.v and poly.v) is the way to
  find all the necessary lemmas.
*)
  by elim=> [ // | n IH p q ]; rewrite //= ?IH karatsuba_split; case: ifP.
Qed.

(* Correctness of karatsuba *)
Lemma karatsubaP p q : karatsuba p q = p * q.
Proof.
(* This proof should be very very easy now that you have proved the recursive
   part correct *)
  exact: karatsuba_recP.
Qed.

End karatsuba.
