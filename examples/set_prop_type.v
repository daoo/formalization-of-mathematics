(* Set is the type of "computational types" *)
Check nat.
Check nat -> nat.
Check bool.
Check bool -> nat.

(* Prop is the type of propositions *)
Check (forall (x : nat), x <> S x).
Check (forall (P : Prop), P -> P).
Check (true <> false).

(* Type is the type of Set and Prop (and Type of Type_n has type Type_(1 + n) *)
Check Set.
Check Prop.
Check Type.


(* 
The difference between Prop and Set is that Prop is "impredicative" which means
that when quantifying over P : Prop in a Prop this quantification is quantifying
over _itself_ as well. This kind of circularity can in some cases lead to
inconsistencies (i.e. that False is provable), compare with Russels paradox. To
avoid this impredicativity in Coq is restricted to Prop (which is ok). This
means that neither Set nor Type are impredicative. Note that Agda is completely
predicative.

Nice examples of impredicativity of Prop can be found in:
   https://sympa.inria.fr/sympa/arc/coq-club/2012-07/msg00129.html

The simplest one follow below:
*)

Definition ModusPonens_Prop := forall P Q : Prop, (P -> Q) -> P -> Q.

 (* This is a Prop *)
Check ModusPonens_Prop.

Theorem ModusPonens_Prop_proof : ModusPonens_Prop.
Proof. unfold ModusPonens_Prop; auto. Qed.

(* It can be applied to itself, i.e., P and Q can be instantiated to
   ModusPonens_Prop. *)
Check ModusPonens_Prop_proof ModusPonens_Prop ModusPonens_Prop.

(* The same thing for Set: *)
Definition ModusPonens_Set := forall P Q : Set, (P -> Q) -> P -> Q.

(* This is a Type... *)
Check ModusPonens_Set.

Theorem ModusPonens_Set_proof : ModusPonens_Set.
Proof. unfold ModusPonens_Set; auto. Qed.

(* So the following is not possible as ModusPonens_Set is a Type, not a Set: *)
(* Check ModusPonens_Set_proof ModusPonens_Set ModusPonens_Set. *)

(* The same for Type *)
Definition ModusPonens_Type := forall P Q : Type, (P -> Q) -> P -> Q.

(* This is also a Type, but with higher level. Sadly the level cannot be seen in
   Coq... But if P and Q above have Type_m then ModusPonens_Type has Type_n with
   the constraint that m < n *) 
Check ModusPonens_Type.

Theorem ModusPonens_Type_proof : ModusPonens_Type.
Proof. unfold ModusPonens_Type; auto. Qed.

(* This produces an error because ModusPonens_Type_proof is expecting things of
   type Type_m but ModusPonens_proof has type Type_n where m < n *)
(* Check ModusPonens_Type_proof ModusPonens_Type ModusPonens_Type. *)
