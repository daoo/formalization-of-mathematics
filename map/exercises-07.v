Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype.
Require Import finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section arith.
(* A few arithmetic lemmas. *)

Lemma ex_arith1 : forall k n, 0 < k < n -> 0 < n - k < n.
Proof.
  by move=> k n /andP [Hk0 Hkn]; rewrite subn_gt0 Hkn /= -{2}[n]subn0 ltn_sub2l // (ltn_trans Hk0 Hkn).
Qed.

Lemma ex_arith2 : forall k n, (0 < k < n) = (0 < n - k < n).
Proof.
  move=> k n.
  apply/idP/idP.
    by apply: ex_arith1.
  move/andP => [H1 H2].
  apply/andP; split; last by rewrite -subn_gt0.
  move: H2 {H1}. case: k => //.
  by rewrite subn0 ltnn.
Qed. 

Lemma ord_to_nat : forall n p (i : 'I_n.+1) (j : 'I_p.+1), i + j < (n + p).+1.

Lemma ord_to_nat2 : forall n (i : 'I_n), i + n < 2 * n.

End arith.

(* simples lemmas about fintype *)


Section fintype.

Lemma inj_card_le (I J : finType) (f : I -> J) : injective f -> #|I| <= #|J|.

Lemma ord1 : forall i : 'I_1, i = ord0.

End fintype.

Section finset.

Variable T: finType.

(* state and prove that E anf being finite sets :
E ∪ F = (E − F) ∪ (E ∩ F) ∪ (F − E).   *)


(* state and prove that 
card(E ∪ F) = card E + card F - card(E ∩ F). *)

Lemma adds: forall (a b : T) (E : {set T}), a != b -> a \notin E -> b \notin E ->
#| a |:  (b |: E)| = #|E| + 2.

End finset.

