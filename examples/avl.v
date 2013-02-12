Require Import Arith ZArith Orders.

Section bin_tree.
  Inductive bin_tree (X: Type) : Type :=
    | bt_nil: bin_tree X
    | bt_node: X -> bin_tree X -> bin_tree X -> bin_tree X.

  Implicit Arguments bt_nil [[X]].
  Implicit Arguments bt_node [[X]].

  Fixpoint node_count {X: Type} (t: bin_tree X) : nat :=
    match t with
    | bt_nil        => 0
    | bt_node _ a b => 1 + node_count a + node_count b
    end.

  Fixpoint tree_height {X: Type} (t: bin_tree X) : nat :=
    match t with
    | bt_nil        => 0
    | bt_node _ a b => 1 + max (tree_height a) (tree_height b)
  end.

  Theorem bin_tree_height_le_count: forall X: Type, forall t: bin_tree X,
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

  Fixpoint search {X: Compare} (x: X) (t: bin_tree X) : option X :=
    match t with
    | bt_nil        => None
    | bt_node y a b => if x < y then search a
                  else if x > y then search b
                     else y
  end.

  Section avl.
    Open Scope Z_scope.

    Definition balance_factor {X: Type} (t: bin_tree X) : Z :=
      match t with
      | bt_nil        => 0
      | bt_node _ a b => Z.of_nat (tree_height a) - Z.of_nat (tree_height b)
      end.

    Definition is_balanced {X: Type} (t: bin_tree X) : Prop :=
      -1 <= balance_factor t <= 1.

    Inductive AVL {X: Type} : bin_tree X -> Prop :=
      | avl_nil: AVL bt_nil
      | avl_node: forall n, is_balanced n -> AVL n.

    Fixpoint avl_insert {X: Type} (x: X) (t: bin_tree X) : bin_tree X :=
      match
  End avl.
End bin_tree.
