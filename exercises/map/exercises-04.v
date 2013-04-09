(* -------------------------------------------------------------------- *)
Require Import ssreflect eqtype ssrbool ssrnat ssrfun path.

(* -------------------------------------------------------------------- *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* For this section:                                                    *)
(*   only move=> h, move/V: h => h, case/V: h, by ... allowed           *)
(* -------------------------------------------------------------------- *)
Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  move=> P Q. case => Hpq Hqp. by move/Hpq.
Qed.

Goal forall (P : nat -> Prop) (Q : Prop),
     (P 0 -> Q)
  -> (forall n, P n.+1 -> P n)
  -> P 4 -> Q.
Proof.
  move=> P Q H1 H2. by do ?move/H2.
Qed.

Goal forall (b b1 b2 : bool), (b1 -> b) -> (b2 -> b) -> b1 || b2 -> b.
Proof. (* No case analysis on b, b1, b2 allowed *)
  move=> b b1 b2 H1 H2 H.
  case/orP: H.
    by move/H1.
    by move/H2.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y /\ p2 y) /\ Q x) -> p1 x && p2 x.
Proof.
  move=> Q p1 p2 n H.
  case: H. move=> H. move/H.
  by move/andP.
Qed.

Goal forall (Q : nat -> Prop) (p1 p2 : nat -> bool) x,
  ((forall y, Q y -> p1 y \/ p2 y) /\ Q x) -> p1 x || p2 x.
Proof.
  move=> Q p1 p2 x H.
  case: H. move=> H. move/H.
  by move/orP.
Qed.

(* -------------------------------------------------------------------- *)
(* No xxxP lemmas allowed                                               *)
(* -------------------------------------------------------------------- *)
Print reflect.
Lemma myidP: forall (b : bool), reflect b b.
Proof.
  case.
    exact: ReflectT.
    exact: ReflectF.
Qed.

Lemma mynegP: forall (b : bool), reflect (~ b) (~~ b).
Proof.
  case.
    exact: ReflectF.
    exact: ReflectT.
Qed.

Lemma myandP: forall (b1 b2 : bool), reflect (b1 /\ b2) (b1 && b2).
Proof.
  move=> b1 b2. case: b1.
  case: b2.
    exact: ReflectT.
    apply: ReflectF. move=> h. by case h.
  case: b2.
    apply: ReflectF. move=> h. by case h.
    apply: ReflectF. move=> h. by case h.
Qed.

Lemma myiffP:
  forall (P Q : Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  move=> P Q b Pb PQ QP.
  move: Pb. case: b.
    case.
      move/PQ => hp. by apply: ReflectT.
      move=> hNp. apply: ReflectF. move/QP => hp. by move/hNp: hp.
    case.
      move/PQ => hp. by apply: ReflectT.
      move=> hNp. apply: ReflectF. move/QP => hp. by move/hNp: hp.
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint len (n m : nat) : bool :=
  match n, m with
  | 0    , _     => true
  | n'.+1, 0     => false
  | n'.+1, m'.+1 => len n' m'
  end.

Lemma lenP: forall n m, reflect (exists k, k + n = m) (len n m).
Proof.
  move=> n; elim: n.
    move=> m. apply: (iffP idP).
      move=> _. by exists m.
      by [].
    move=> n IH m. apply: (iffP idP).
      case: m. by [].
        move=> m /= le_nm. move/IH: le_nm=> le_nm.
        case: le_nm. move=> k eq_xk_m. exists k.
        by rewrite -eq_xk_m addnS.
      case: m.
        case. move=> k. by rewrite addnS.
        move=> m h. case: h => k.
        rewrite addnS. move=> eq_kSn_k. case: eq_kSn_k.
        move=> eq_kn_m. apply/IH. by exists k.
Qed.

(* --------------------------------------------------------------------*)
Lemma snat_ind : forall (P : nat -> Prop),
  (forall x, (forall y, y < x -> P y) -> P x)
  -> forall x, P x.
Proof.
  (* Hint: strengthen P x into (forall y, y <= x -> P x) and then
   *       perform the induction on x. *)
  move=> P ind x; move: {-2}x (leqnn x); elim: x.
    + move=> x. rewrite leqn0. move/eqP=> z_x.
      rewrite z_x. by apply: ind.
    + move=> n IHn x. rewrite leq_eqVlt. move=> h. case/orP: h.
      * move=> eq_x_Sn. rewrite (eqP eq_x_Sn). apply ind.
        move=> y. rewrite ltnS. by move/IHn.
      * rewrite ltnS. by move/IHn.
Qed.

Lemma odd_ind : forall (P : nat -> Prop),
  P 0 -> P 1 -> (forall x, P x  -> P x.+2)
  -> forall x, P x.
Proof.
  move=> P p0 p1 ind. elim/snat_ind.
  move=> x; case: x.
    + by [].
    + move=> x; case: x.
      * by [].
      * move=> x h. apply ind. by apply h.
Qed.

Lemma oddSS : forall n, odd n.+2 = odd n.
Proof.
  move=> n. by rewrite /= negbK.
Qed.

Lemma odd_add : forall m n, odd (m + n)  = odd m (+) odd n. (* using odd_ind *)
Proof.
  elim/odd_ind.
    by [].
    by [].
    move=> M IHm n. by rewrite !oddSS IHm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma nat_ind2: forall (P : nat -> Prop),
  P 0 -> P 1 -> (forall p, P p -> P p.+1 -> P p.+2)
  -> forall n, P n.
Proof.
  move=> P p0 p1 ind. elim/snat_ind.
  move=> x; case: x.
    + by [].
    + move=> x; case: x.
      * by [].
      * move=> x h. apply ind.
        by apply h. by apply h.
Qed.

Fixpoint fib n :=
  match n with
  | 0              => 1
  | 1              => 1
  | (n.+1 as p).+1 => fib p + fib n
  end.

Lemma fib0: fib 0 = 1.
Proof. by []. Qed.

Lemma fib1: fib 1 = 1.
Proof. by []. Qed.

Lemma fibSS: forall n, fib n.+2 = fib n.+1 + fib n.
Proof. by []. Qed.

Goal
  forall p q,
    (fib (p.+1 + q.+1))
    = (fib p.+1) * (fib q.+1) + (fib p) * (fib q).
Proof.
  elim/nat_ind2.
    move=> q. by rewrite add1n fib1 fib0 !mul1n fibSS.
    move=> q. rewrite add2n !fibSS !fib1 !fib0.
    by rewrite add1n mul2n mul1n -addnn addnAC.
    move=> p IHp IHSp q.
    rewrite 2!addSn fibSS -addSn IHp IHSp.
    rewrite !fibSS !mulnDl -!addnA.
    by rewrite (addnCA (fib p.+1 * fib q) _ _).
Qed.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)
