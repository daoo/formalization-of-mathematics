(* Require part *)
Require Import ssreflect eqtype ssrbool.

(* some magic settings *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Checking *)

Check True.
Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3,4).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3,3=5): nat * Prop.
Check (fun x:nat => x = 3).
Check (forall x:nat, x < 3 \/(exists y:nat, x = y + 3)).

Locate "_ && _".

About and.

Check (and True False).

Section simple_proofs.
(* Using only move apply  by *)

Variables P Q R S : Prop.

Lemma id_P : P -> P. Proof. done. Qed.

 Lemma id_PP : (P -> P) -> P -> P. Proof. done. Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> Hpq Hqr Hp.
  by apply/Hqr/Hpq.
Qed.

Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
Proof.
  move=> Hpqr Hq Hp.
  by apply/Hpqr.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  move=> Hpr Hp Hq.
  by apply/Hpr.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  move=> Hppq Hp.
  by apply: Hppq.
Qed.

Lemma delta_impR : (P -> Q) -> P -> P -> Q.
Proof.
  move=> Hpq Hp1 Hp2.
  by apply: Hpq.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
  move=> Hpq Hpr Hqrs Hp.
  apply: Hqrs.
  - by apply: Hpq.
  - by apply: Hpr.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  move=> H.
  apply: (H) => H0.
  apply: H0 => H1.
  by apply: H.
Qed.

Check diamond.
End simple_proofs.

Check diamond.

Section haveex.

Variables P Q R T : Prop.
Hypothesis H : P -> Q.
Hypothesis H0 : Q -> R.
Hypothesis H1 : (P -> R) -> T -> Q.
Hypothesis H2 : (P -> R) -> T.

Lemma Q0 : Q.
Proof.
  apply: H1.
  move=> Hp.
  apply: H0.
  by apply: H.
  apply: H2 => Hp.
  apply: H0.
  by apply: H.
Qed.

Lemma Q1 : Q.
Proof.
  have Hp: (P -> R) by move=> p; apply H0; apply H.
  have Ht: T by apply: H2.
  by apply H1.
Qed.
  

 Print Q0.

 Print Q1.

End haveex.

(* Using also case rewrite *)

Section boolex.

(*                  a && b == the boolean conjunction of a and b.             *)
(*                  a || b == then boolean disjunction of a and b.            *)
(*                 a ==> b == the boolean implication of b by a.              *)
(*                    ~~ a == the boolean negation of a.                      *)
(*                 a (+) b == the boolean exclusive or (or sum) of a and b.   *)


Theorem bool_xor_not_eq :
forall b1 b2,  (b1 (+) b2) = ~~(b1 == b2).
Proof.
  move=> b1 b2. case: b1.
    by case: b2.
  by case: b2.
Qed.

Theorem bool_not_and :
 forall b1 b2:bool,
   ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
  by case.
Qed.

Theorem bool_not_not (b:bool): ~~ (~~ b) = b.
Proof.
  by case: b.
Qed.

Theorem bool_ex_middle : forall b:bool,  b || (~~ b) = true.
Proof.
  by case.
Qed.

Theorem bool_eq_reflect : forall b1 b2:bool, (b1 == b2) = true -> b1 = b2.
Proof.
  by move=> b1 b2; case b1; case b2.
Qed.

Theorem bool_eq_reflect2 : forall b1 b2:bool, b1 = b2 ->  (b1 == b2) = true.
Proof.
  by move => b1 b2 E; rewrite E eqxx.
Qed.

Theorem bool_not_or :
 forall b1 b2:bool,
   ~~ ( b1 || b2) =  (~~ b1) && (~~ b2).
Proof.
  by case; case.
Qed. 

Theorem bool_distr :
 forall b1 b2 b3:bool,
    (b1 && b3) ||(b2 && b3) =  (b1 || b2) && b3.
Proof.
  by case; case; case.
Qed.

End boolex.

(* Mixing Prop and bool *)
(* Set Printing Coercions. *)
Section bool_prop.

Check (forall (a b : bool), a -> b).
Notation "x 'is_true'" := (is_true x) (at level 8).
Check (forall (a b : bool), a is_true ->  b is_true).
Lemma Andb_idl (a b : bool) : (b is_true -> a is_true ) -> a && b = b.
Proof.
  case: a; case: b; rewrite //=.
  by move=> H; rewrite H.
Qed.

Lemma Andb_idr (a b :bool) : (a is_true-> b is_true) -> a && b = a.
Proof.
  case: a; case: b; rewrite //=.
  by move=> H; rewrite H.
Qed.

Lemma Andb_id2l (a b c : bool) : (a -> b = c) -> a && b = a && c.
Proof.
  case: a; case: b; case: c; rewrite //=.
  by move=> H; rewrite H.
  by move=> H; rewrite H.
Qed.

End bool_prop.

Section more_prop.

Lemma and_imp_dist : forall A B C D:Prop,
                     (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
  move=> A B C D H.
  case: H => Hab Hcd Hac.
  case: Hac => Ha Hc.
  split.
    by apply Hab.
  exact: Hcd.  
Qed.

Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
Proof.
  move=> A.
  move=> H.  
  case: H => Ha Hna.
  done.
Qed.

Lemma or_and_not : forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
  move=> A B H.
  case: H => Haob Hna.
  by case: Haob.
Qed.

Lemma or_imp_dist : forall A B C D:Prop,
                     (A -> B) \/ (C -> D) -> A /\ C -> B \/ D.
Proof.
  move=> A B C D H.
  case: H => H1 Hac.
    case: Hac => Ha Hc.
    left.  
    by apply H1.
  right.
  case: Hac => Ha Hc.
  by apply: H1.
Qed.

  Section more_prop.

