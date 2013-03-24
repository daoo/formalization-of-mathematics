Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun div path bigop prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The following lemma is already proved as in the examples file, but you may
  want to prove it in a different way, by induction on n.

  This lemma also exists in the library (part of binomial.v) *)

Lemma sumP' : forall n, \sum_(i < n) i = (n * n.-1) ./2.
Proof.
Qed.

(* You can prove this one in two fashions.
   1/ by induction on n.
   2/ by spliting and distributivity, then re-using sumP'.  But division by
   two is a pain in the neck.  *)
Lemma sum_odd1 : forall n, \sum_(i < n) (2 * i + 1) = n ^ 2.

Lemma ex1 : forall n f, \sum_(i < n) (f i + 1) = n + \sum_(i < n) f i.

Lemma fact_big : forall n, n`! = \prod_(1 <= i < n.+1) i.

(* use the previous lemma for this proof. This is an opportunity to use big_prop. *)
Lemma prime_lt_Ndiv_fact :

Lemma sum_exp : forall x n, 0 < x -> x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.

Section abstract.

Variable A : Type.
Variables ad mu : A -> A -> A.
Variable op : A -> A.
Variables a0 a1 : A.

Hypothesis adC : commutative ad.
Hypothesis muC : commutative mu.
Hypothesis adA : associative ad.
Hypothesis muA : associative ad.
Hypothesis ad0a : left_id a0 ad.
Hypothesis ada0 : right_id a0 ad.
Hypothesis mu0a : left_zero a0 mu.
Hypothesis mua0 : right_zero a0 mu.
Hypothesis mu1a : left_id a1 mu.
Hypothesis mua1 : right_id a1 mu.
Hypothesis mu_adl : left_distributive mu ad.
Hypothesis mu_adr : right_distributive mu ad.
Hypothesis adN : forall a, ad a (op a) = a0.

Variable exp : A -> nat -> A.
Hypothesis exp0 : forall x, exp x 0 = a1.
Hypothesis expS : forall x n, exp x n.+1 = mu x (exp x n).
Hypothesis muVop1 : forall x, op x = mu (op a1) x.

Local Notation "x ^ n" := (exp x n).
Local Notation "a + b" := (ad a b).
Local Notation "a * b" := (mu a b).
Local Notation "a - b" := (ad a (op b)).

(* Add the relevant canonical structures to allow using natural operations on
  this addition, and multiplication.  *)

(* If you added enough canonical structures, this should be provable using
    big_split big_distrr, big_ord_recl, big_ord_recr, and many of the 
    hypotheses given above. *)

Lemma sum_exp' : forall x n,  x ^ n.+1 - a1 = (x - a1) * \big[ad/a0]_(i < n.+1) x ^ i.

End abstract.