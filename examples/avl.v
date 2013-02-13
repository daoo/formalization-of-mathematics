Require Import Arith ZArith Compare_dec.

Section Tree.
  Inductive tree (A: Type) : Type :=
    | Leaf: tree A
    | Node: A -> tree A -> tree A -> tree A.

  Implicit Arguments Leaf [[A]].
  Implicit Arguments Node [[A]].

  Fixpoint node_count {A: Type} (t: tree A) : nat :=
    match t with
    | Leaf       => 0
    | Node _ a b => 1 + node_count a + node_count b
    end.

  Fixpoint tree_height {A: Type} (t: tree A) : nat :=
    match t with
    | Leaf       => 0
    | Node _ a b => 1 + max (tree_height a) (tree_height b)
  end.

  Theorem tree_height_le_count: forall {A: Type}, forall t: tree A,
    tree_height t <= node_count t.
  Proof.
    intros X t. induction t as [| x a IHa b].
      simpl. reflexivity.
      simpl.
      apply Le.le_n_S.
      apply Max.max_case_strong.
        intro H. rewrite IHa. apply le_plus_l.
        intro H. rewrite IHb. apply le_plus_r.
  Qed.

  Section Search.
    Inductive

    Fixpoint search (x: nat) (t: tree nat) : option nat :=
      match t with
      | Leaf       => None
      | Node y a b => match nat_compare x y with
        | Lt => search x a
        | Eq => Some y
        | Gt => search x b
      end
    end.

    Fixpoint insert (x: nat) (t: tree nat) : tree nat :=
      match t with
      | Leaf       => Node x Leaf Leaf
      | Node y a b => match nat_compare x y with
        | Lt => Node y (insert x a) b
        | Eq => Node x a b
        | Gt => Node y a (insert x b)
      end
    end.

    Lemma nat_compare_refl: forall n: nat,
      nat_compare n n = Eq.
    Proof.
      intros n. induction n as [| n'].
        reflexivity.
        simpl. apply IHn'.
    Qed.

    Theorem insert_search: forall (x: nat), forall (t: tree nat),
      search x (insert x t) = Some x.
    Proof.
      intros x t. induction t as [| y a IHa b IHb].
        (* t = Leaf *)
        simpl. rewrite -> nat_compare_refl. reflexivity.
        (* t = Node y a b *)
        simpl. remember (nat_compare x y) as eq. destruct eq.
          (* Eq *) simpl. rewrite nat_compare_refl. reflexivity.
          (* Lt *) simpl. rewrite <- Heqeq. rewrite IHa. reflexivity.
          (* Gt *) simpl. rewrite <- Heqeq. rewrite IHb. reflexivity.
    Qed.
  End Search.

  Section AVL.
    Open Scope Z_scope.

    Definition balance_factor (t: tree A) : Z :=
      match t with
      | Leaf       => 0
      | Node a _ b => Z.of_nat (tree_height a) - Z.of_nat (tree_height b)
      end.

    Definition is_balanced (t: tree A) : Prop :=
      -1 <= balance_factor t <= 1.

    Inductive AVL : tree A -> Prop :=
      | avl_nil: AVL Leaf
      | avl_node: forall n, is_balanced n -> AVL n.

    Fixpoint avl_insert (x: A) (t: tree A) : tree A :=
      match
  End AVL.
End Tree.
