Require Import List Recdef Div2 Setoid Omega Permutation.
Set Implicit Arguments.


(** Morphisms are handly since we can use rewrite to massage the goal
  * and the hypotheses.
 **)
(*
(* The following are now in the standard library. *)
Add Parametric Relation A: (list A) (@Permutation A)
   reflexivity proved by (@Permutation_refl A)
   symmetry proved by (@Permutation_sym A)
   transitivity proved by (@perm_trans A)
 as perm_rel.

Add Parametric Morphism A: (@cons A)
  with signature (@eq A) ==> (@Permutation A) ==> (@Permutation A)
  as cons_mor.
Proof.
  intros; apply perm_skip; assumption.
Qed.

Add Parametric Morphism A: (@length A)
  with signature (@Permutation A) ==> (@eq nat)
  as length_mor.
Proof.
  intros; apply Permutation_length; assumption.
Qed.
*)
Add Parametric Morphism A: (@app A)
  with signature (@Permutation A) ==> (@Permutation A) ==> (@Permutation A)
  as app_mor.
Proof.
  intros; apply Permutation_app; assumption.
Qed.

(* When we want to apply ex falso to a false arithmetic expression. *)
Tactic Notation "omega_false" :=
  let F:=fresh "omega_false"
  in assert (F: 0%nat=1%nat);
     [ omega | discriminate F ].

(* A custom tactic to unfold / eta-expand pairs. *)
Ltac pair_tac :=
  match goal with
   | [ |-  context [match ?l with (x,y) => (?a::x,?b::y) end] ]
          => replace (let (x,y):=l in (a::x,b::y))
                 with (a::fst l,b::snd l); simpl;
               [idtac | destruct l; simpl; reflexivity]
   | [ H:context [match ?l with (x,y) => (?a::x,?b::y) end] |- ?g]
          => replace (let (x,y):=l in (a::x,b::y))
                 with (a::fst l,b::snd l) in H; simpl;
               [idtac | destruct l; simpl; reflexivity]
   | [ H: (?x,?y) = ?E |- context [fst ?E] ]
          => replace (fst E) with x; [idtac | rewrite <- H; reflexivity]
   | [ H: ?E = (?x,?y) |- context [fst ?E] ]
          => replace (fst E) with x; [idtac | rewrite H; reflexivity]
   | [ H: (?x,?y) = ?E |- context [snd ?E] ]
          => replace (snd E) with y; [idtac | rewrite <- H; reflexivity]
   | [ H: ?E = (?x,?y) |- context [snd ?E] ]
          => replace (snd E) with y; [idtac | rewrite H; reflexivity]
   | [ H: ?E = (?x,?y) |- ?g ]
          => replace x with (fst E); [idtac | rewrite H; reflexivity];
             replace y with (snd E); [idtac | rewrite H; reflexivity]
  end.

Definition transitive (A:Type) (rel: A -> A -> bool) :=
  forall x y z, rel x y = true -> rel y z = true -> rel x z = true.

Definition antisym (A:Type) (rel: A -> A -> bool) :=
  forall x y, rel x y = true -> rel y x = true -> x = y.

(* A custom inductive scheme working on two lists with the same length. *)
Theorem ind_2list A: forall P: list A -> list A -> Prop,
  P nil nil
    -> (forall l l' a b, P l l' -> P (a::l) (b::l'))
    -> forall l l', length l = length l' -> P l l'.
Proof.
  intros P ? Pi l l' Hle.
  do 2 generalize Hle; set (n:=length l') in Hle|-*.
  unfold n at 2; clear Hle; generalize n; clear n; intro n; revert l l'.
  induction n; intros l l' ? ?.
    destruct l; destruct l'; simpl in *|-; discriminate || auto.
 destruct l; destruct l'; simpl in *|-; discriminate || auto.
Qed.

Section sort.
  Variable A: Type.
  Variable order: A -> A -> bool.
  Notation "x << y" := (order x y) (at level 70).

  Variable order_total: forall a b, {(a<<b)=true} + {(b<<a)=true}.

  Lemma false2true: forall a b, (a<<b)=false -> (b<<a)=true.
  Proof.
    intros a b H.
    destruct (order_total a b) as [Hf|]; auto.
    rewrite Hf in H; discriminate.
  Qed.
  Hint Resolve order_total false2true: order.

  (** A naive definition for sorted lists. **)
  Inductive Sorted: list A -> Prop :=
    |sorted_nil: Sorted nil
    |sorted_singl: forall a, Sorted (a::nil)
    |sorted_ind: forall a b l, (a<<b)=true -> Sorted (b::l)
                                           -> Sorted (a::b::l).
  Hint Resolve sorted_nil sorted_singl sorted_ind: sort.

  (* Some easy lemmas. *)
  Lemma sorted_hd: forall a q,
    Sorted q -> (a<<hd a q)=true -> Sorted (a::q).
  Proof.
    intros a [|] Hq H; simpl;
      try apply sorted_ind; auto with sort.
  Qed.

  Lemma sorted_hd_rm: forall l a,
    Sorted (a::l) -> Sorted l.
  Proof.
    intros [|?[|]] a H; auto with sort.
    inversion H; assumption.
  Qed.
  Hint Resolve sorted_hd sorted_hd_rm: sort.

  Lemma sorted_split_rm: transitive order ->
    forall l l' a, Sorted (l++a::l') -> Sorted (l++l').
  Proof.
    intros Ho l l' a H; induction l as [|? l IH]; simpl in *|-*.
      inversion H; auto with sort.
    destruct l; simpl in *|-*; auto with sort.
      destruct l'; simpl; auto with sort.
      inversion H as [| |? ? ? ? H'].
      inversion H'; constructor; auto.
      apply Ho with (y:=a); assumption.
    inversion H as [| |? ? ? ? H']; apply IH in H'.
    constructor; auto.
  Qed.

  Lemma sorted_in: transitive order ->
    forall a l, Sorted (a::l) -> forall x, In x l -> (a<<x)=true.
  Proof.
    intros Ho a l H x Hin; induction l as [|b q IH].
      inversion Hin.
    destruct (in_inv Hin) as [Hin'|Hin'].
      rewrite <- Hin'; inversion H; assumption.
    apply IH; auto.
    change (a::q) with ((a::nil)++q).
    apply sorted_split_rm with (a:=b); simpl; auto.
  Qed.

  Lemma sorted_split: forall l x l', Sorted l -> Sorted l' ->
      (forall a, In a l -> (a<<x)=true) ->
      (forall a', In a' l' -> (x<<a')=true) ->
    Sorted (l++x::l').
  Proof.
    intros l x l'; revert l; induction l as [|? l IH];
      intros Hs Hs' Hin Hin'; simpl.
      destruct l'; auto with sort.
      constructor; auto; apply Hin'; simpl; auto.
    destruct l; simpl in *|-*.
      apply sorted_hd; simpl.
        destruct l'; auto with sort.
      apply Hin; simpl; auto.
    constructor.
      inversion Hs; auto.
    apply IH; auto || inversion Hs; auto.
  Qed.


  Lemma perm_singl: forall (a:A) l, Permutation (a::nil) l -> l=a::nil.
  Proof.
    intros a [|?[|]] H.
        symmetry in H; elim (Permutation_nil_cons H).
      destruct (Permutation_in _ H (in_eq a nil)) as [|Hf].
        f_equal; assumption.
      elim Hf.
    assert (Hf:=Permutation_length H); simpl in Hf; discriminate.
  Qed.

  (* Sorting is unique. *)
  Theorem sorted_uniq: transitive order -> antisym order ->
    forall l l', Permutation l l' -> Sorted l -> Sorted l' -> l=l'.
  Proof.
    intros Ho Ha l l' Hll'.
    assert(Hle:=Permutation_length Hll').
    revert l l' Hle Hll'.
    apply (ind_2list
            (fun l l' => Permutation l l'->Sorted l->Sorted l'->l=l'));
      auto.
    intros l l' a b H Hll' Hl Hl'.
    assert(Hab:a=b).
      assert(Hin: In a (b::l')).
        apply (Permutation_in (l:=a::l)); [idtac | simpl]; auto.
      simpl in Hin; destruct Hin as [|Hin]; auto.
      assert(Hin': In b (a::l)).
        apply (Permutation_in (l:=b::l')); [symmetry | simpl]; auto.
      simpl in Hin'; destruct Hin' as [|Hin']; auto.
      apply Ha; [apply (sorted_in Ho Hl) | apply (sorted_in Ho Hl')]; auto.
    rewrite Hab in *|-*; clear Hab; f_equal.
    apply H.
    exact (Permutation_cons_inv Hll').
    exact (sorted_hd_rm Hl).
    exact (sorted_hd_rm Hl').
  Qed.


  Section insert.
    (** Insert sort **)

    Fixpoint insert (x:A) (l:list A) {struct l} : list A :=
      match l with
        nil  => x::nil
      | a::q => if x << a
                then x :: l
                else a :: insert x q
      end.
     Functional Scheme insert_ind := Induction for insert Sort Prop.

    Fixpoint insert_sort l : list A :=
      match l with
        nil  => nil
      | a::q => insert a (insert_sort q)
      end.

    (** It permutes the input list **)
    Theorem insert_sort_perm: forall l, Permutation l (insert_sort l).
    Proof.
      intro l; induction l as [|a l IH]; simpl.
      reflexivity.
      set(l':=l); unfold l' at 1; rewrite IH; unfold l'; clear l'.
      set(l':=insert_sort l); clear IH.
      functional induction insert a l' as [| | ? ? ? ? ? IH];
        simpl; try reflexivity.
     rewrite <- IH; constructor.
    Qed.

    Lemma insert_hd: forall a x l,
      hd x (insert a l) = a   \/   hd x (insert a l) = hd x l.
    Proof.
      intros a ? l.
      functional induction insert a l; simpl; auto.
    Qed.

    (** Correction of 'insert' **)
    Lemma insert_correct: forall a l,
      Sorted l -> Sorted (insert a l).
    Proof.
      intros a l.
      functional induction insert a l as [| | l b [|c q] _ Hb IH];
        simpl; auto with sort; intro H.
        constructor; auto with sort order.
      apply sorted_hd.
        apply IH; exact (sorted_hd_rm H).
      destruct (insert_hd a b (c::q)) as [H0|H0];
        simpl in H0; rewrite H0; auto with order.
      inversion H; assumption.
    Qed.

    (** Correction of 'insert_sort' **)
    Theorem insert_sort_correct: forall l, Sorted (insert_sort l).
    Proof.
      intro l; induction l; simpl; auto with sort.
      apply insert_correct; assumption.
    Qed.
  End insert.


  Section merge.
    (** Merge sort. **)

    (** Division into 2 lists of ~1/2 length. **)
    Fixpoint divide (l:list A) {struct l} : list A*list A :=
      match l with
        nil     => (nil, nil)
      | a::nil  => (a::nil, nil)
      | a::b::q => let (q1,q2):=divide q
                   in (a::q1, b::q2)
      end.
    Functional Scheme divide_ind := Induction for divide Sort Prop.


    (** Length conservation. **)
    Lemma divide_sum: forall (l:list A),
      length l = length (fst (divide l)) + length (snd (divide l)).
    Proof.
      intro l; functional induction divide l as [| | ? ? ? ? ? ? ? IH]; simpl; auto.
      rewrite IH; do 2 pair_tac; auto with arith.
    Qed.

    (** Divide is balanced. **)
    Theorem divide_balanced: forall (l:list A),
      length (fst (divide l)) <=  S (div2 (length l))
           /\ length (snd (divide l)) <= div2 (length l).
    Proof.
      intro l; functional induction divide l; simpl; auto.
      pair_tac; omega.
    Qed.

    (** Divide returns a partitition of the input list. **)
    Lemma divide_perm: forall l:list A,
      Permutation l (fst (divide l) ++ snd (divide l)).
    Proof.
      intro l; functional induction divide l as [| | ? ? ? ? ? ? ? IH];
        simpl; try reflexivity.
      pair_tac; rewrite (Permutation_cons_app _ _ _ IH); reflexivity.
    Qed.

    Definition sum_length A (c:(list A)*(list A)) := length (fst c) + length (snd c).

    (** Merge of 2 lists; if the inputs are sorted, so is the output. **)
    (* It would be better to use nested structural inductions, but 'functional
     * scheme' does not support higher order (currified) elimination principles.
     *)
    Function merge (c: (list A)*(list A)) {measure sum_length c} : list A :=
      let (l1,l2) := c
      in
      match l1 with
        nil    => l2
      | h1::t1 =>
            match l2 with
              nil    => l1
            | h2::t2 => if h1 << h2
                        then h1 :: merge (t1,l2)
                        else h2 :: merge (l1,t2)
            end
      end.
    Proof.
      (* Now, we have to prove that the recursive calls are smaller. *)
      unfold sum_length; intros; simpl; omega.
      unfold sum_length; intros; simpl; omega.
    Defined.

    (** The output is a concatenation of the inputs, modulo permutation. **)
    Lemma merge_perm: forall c,
      Permutation (merge c) (fst c ++ snd c).
    Proof with try reflexivity.
      intro c; functional induction merge c; simpl in *|-*...
          rewrite <- app_nil_end...
        constructor; assumption.
      rewrite <- Permutation_cons_app; [idtac|reflexivity]; rewrite perm_swap.
      constructor; assumption.
    Qed.

    Lemma merge_hd: forall c x,
      hd x (merge c) = hd x (fst c)   \/   hd x (merge c) = hd x (snd c).
    Proof with auto.
      intro c; functional induction merge c; simpl...
    Qed.

    (* Merge is correct. *)
    Lemma merge_correct: forall c,
      Sorted (fst c) -> Sorted (snd c) -> Sorted (merge c).
    Proof.
      intro c; functional induction merge c
        as [| | ? ? ? ? h1 t1 ? ? ? ? ? IH | ? ? ? ? h1 t1 ? h2 t2 ? ? IH];
        simpl in *|-*; auto; intros Hs1 Hs2; apply sorted_hd.
            apply IH; eauto with sort.
          destruct t1; auto.
          match goal with [ |- context [merge ?c] ] => destruct (merge_hd c h1) as [H|H] end;
            rewrite H; simpl; [inversion Hs1|idtac]; auto with sort.

      apply IH; eauto with sort.
      destruct t2; auto with order.
      match goal with [ |- context [merge ?c] ] => destruct (merge_hd c h2) as [H|H] end;
          rewrite H; simpl; [idtac|inversion Hs2]; auto with sort order.
    Qed.

    (** Some trivial lemmas about divide. **)
    Lemma lemma_divide_fst: forall (l:list A),
      1<length l -> length (fst (divide l)) < length l.
    Proof.
      intros [|? [|? l]] ?; simpl in *|-*; try omega_false.
      pair_tac; simpl.
      functional induction divide l;
        intros; simpl; try pair_tac; auto with arith.
    Qed.

    Lemma lemma_divide_snd: forall (l:list A),
      1<length l -> length (snd (divide l)) < length l.
    Proof.
     intros [|? [|? l]] ?; simpl in *|-*; try omega_false.
      pair_tac; simpl.
      functional induction divide l;
        intros; simpl; try pair_tac; auto with arith.
    Qed.

    (** merge_sort **)
    Function merge_sort (l:list A) {measure length l} : list A :=
      match l with
        nil   => nil
      | a::nil => a::nil
      | _ => let (l1,l2):=divide l
             in merge (merge_sort l1,merge_sort l2)
    end.
    Proof.
        intros; pair_tac; apply (lemma_divide_snd); simpl; auto with arith.
      intros; pair_tac; apply (lemma_divide_fst); simpl; auto with arith.
    Defined.

    (** It permutes the input list. **)
    Theorem merge_sort_perm: forall l, Permutation l (merge_sort l).
    Proof.
      intro l; functional induction merge_sort l; simpl; auto; try reflexivity.
      rewrite merge_perm; simpl.
      rewrite (divide_perm l); simpl; do 2 pair_tac.
      apply Permutation_app; assumption.
    Qed.

    (* Correction *)
    Theorem merge_sort_correct: forall l, Sorted (merge_sort l).
    Proof.
      intro l; functional induction merge_sort l; simpl; auto with sort.
      apply merge_correct; simpl; assumption.
    Qed.

  End merge.


  Section quick.
    (** Quick sort **)

    (* Filter the elements less and greater than x. *)
    Fixpoint split x l {struct l} : list A * list A :=
      match l with
        nil  => (nil,nil)
      | h::t => let (ll,lg) := split x t
                in if h<<x then (h::ll,lg)
                           else (ll,h::lg)
      end.
    Functional Scheme split_ind := Induction for split Sort Prop.

    (** Length conservation. **)
    Lemma split_sum: forall x (l:list A),
      length l = length (fst (split x l)) + length (snd (split x l)).
    Proof.
      intros x l; functional induction split x l as [| ? ? ? ? IH | ? ? ? ? IH];
        simpl; auto; rewrite IH; do 2 pair_tac; auto with arith.
    Qed.

    (** Split returns a partitition of the input list. **)
    Lemma split_perm: forall x (l:list A),
      Permutation l (fst (split x l) ++ snd (split x l)).
    Proof.
      intros x l; functional induction split x l as [| ? ? ? ? IH | ? ? ? ? IH];
        simpl; try reflexivity.
        rewrite IH; do 2 pair_tac; reflexivity.
      rewrite (Permutation_cons_app _ _ _ IH); do 2 pair_tac; reflexivity.
    Qed.

    (** Some trivial lemmas about split. **)
    Lemma lemma_split_fst: forall x (l:list A),
      length (fst (split x l)) <= length l.
    Proof.
      intros x l; functional induction split x l;
        simpl; try pair_tac; auto with arith.
    Qed.

    Lemma lemma_split_snd: forall x (l:list A),
      length (snd (split x l)) <= length l.
    Proof.
      intros x l; functional induction split x l;
        simpl; try pair_tac; auto with arith.
    Qed.

    (* Split is correct. *)
    Lemma split_correct_fst: forall x l,
      forall a, In a (fst (split x l)) -> (a<<x)=true.
    Proof.
      intros x l; functional induction split x l as [| ? ? ? ? IH | ? ? ? ? IH];
        intros a H; auto; simpl in *|-*.
        destruct H.
          rewrite <- H; auto.
        apply IH; pair_tac; auto.
      apply IH; pair_tac; auto.
    Qed.

    Lemma split_correct_snd: forall x l,
      forall a, In a (snd (split x l)) -> (x<<a)=true.
    Proof.
      intros x l; functional induction split x l as [| ? ? ? ? IH | ? ? ? ? IH];
        intros a H; auto; simpl in *|-*.
        apply IH; pair_tac; auto.
      destruct H.
        rewrite <- H; auto with order.
      apply IH; pair_tac; auto.
    Qed.

    (* The quick sort itself. *)
    Function quick_sort (l:list A) {measure length l} : list A :=
      match l with
          nil => nil
      | h::t  => let (ll,lg) := split h t
                 in quick_sort ll ++ h :: quick_sort lg
      end.
    Proof.
      intros; pair_tac; eapply le_lt_trans; [apply lemma_split_snd | simpl; auto].
      intros; pair_tac; eapply le_lt_trans; [apply lemma_split_fst | simpl; auto].
    Defined.

    (** It permutes the input list. **)
    Theorem quick_sort_perm: forall l, Permutation l (quick_sort l).
    Proof.
      intro l; functional induction quick_sort l as [| ? ? ? ? ? ? ? IH1 IH2];
        simpl; try reflexivity.
      rewrite <- IH1; rewrite <- IH2.
     pair_tac; apply Permutation_cons_app; apply split_perm.
    Qed.

    (* Correction. *)
    Theorem quick_sort_correct: forall l, Sorted (quick_sort l).
    Proof.
      intro l; functional induction quick_sort l; simpl; auto with sort.
      apply sorted_split; auto || intros ? H;
        [apply (split_correct_fst _ t) | apply (split_correct_snd _ t)]; pair_tac.
      apply (@Permutation_in _ (quick_sort ll)); auto || symmetry; apply quick_sort_perm.
      apply (@Permutation_in _ (quick_sort lg)); auto || symmetry; apply quick_sort_perm.
    Qed.

  End quick.

End sort.


(** Run tests, using the virtual machine (vm_compute). **)

Eval vm_compute
  in insert_sort Compare_dec.leb (3::8::1::7::2::9::6::0::4::9::1::5::nil).

Eval vm_compute
  in (merge_sort Compare_dec.leb (1::9::3::5::6::2::9::1::0::8::4::7::nil)).

Eval vm_compute
  in (quick_sort Compare_dec.leb (3::4::7::0::9::4::3::8::5::1::2::6::nil)).
