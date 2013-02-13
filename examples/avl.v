Require Import Arith ZArith.

Section Tree.
  Inductive tree (X: Type) : Type :=
    | Leaf: tree X
    | Node: X -> tree X -> tree X -> tree X.

  Implicit Arguments Leaf [[X]].
  Implicit Arguments Node [[X]].

  Fixpoint node_count {X: Type} (t: tree X) : nat :=
    match t with
    | Leaf       => 0
    | Node _ a b => 1 + node_count a + node_count b
    end.

  Fixpoint tree_height {X: Type} (t: tree X) : nat :=
    match t with
    | Leaf       => 0
    | Node _ a b => 1 + max (tree_height a) (tree_height b)
  end.

  Theorem tree_height_le_count: forall X: Type, forall t: tree X,
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

  Fixpoint search {X: Type} (x: X) (t: tree X) : option X :=
    match t with
    | Leaf       => None
    | Node y a b => match comp x y with
      | LT => search x a
      | EQ => Some y
      | GT => search x b
    end
  end.

  Fixpoint insert (x: X) (t: tree X) : tree X :=
    match t with
    | Leaf       => Node x Leaf Leaf
    | Node y a b => match comp x y with
      | LT => Node y (insert x a) b
      | EQ => Node x a b
      | GT => Node y a (insert x b)
    end
  end.

  Theorem insert_search: forall (x: X), forall (t: tree X),
    search x (insert x t) = Some x.
  Proof.
    intros x t. induction t as [| y a IHa b].
      simpl. admit.

  Section AVL.
    Open Scope Z_scope.

    Definition balance_factor {X: Type} (t: tree X) : Z :=
      match t with
      | Leaf       => 0
      | Node a _ b => Z.of_nat (tree_height a) - Z.of_nat (tree_height b)
      end.

    Definition is_balanced {X: Type} (t: tree X) : Prop :=
      -1 <= balance_factor t <= 1.

    Inductive AVL {X: Type} : tree X -> Prop :=
      | avl_nil: AVL Leaf
      | avl_node: forall n, is_balanced n -> AVL n.

    Fixpoint avl_insert {X: Type} (x: X) (t: tree X) : tree X :=
      match
  End AVL.
End Tree.
