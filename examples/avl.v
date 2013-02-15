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
    | Node _ l r => 1 + node_count l + node_count r
    end.

  Fixpoint tree_height {X: Type} (t: tree X) : nat :=
    match t with
    | Leaf       => 0
    | Node _ l r => 1 + max (tree_height l) (tree_height r)
  end.

  Theorem tree_height_le_count: forall {X: Type}, forall t: tree X,
    tree_height t <= node_count t.
  Proof.
    intros X t. induction t as [| x l IHl r IHr].
      simpl. reflexivity.
      simpl.
      apply Le.le_n_S.
      apply Max.max_case_strong.
        intro H. rewrite IHl. apply le_plus_l.
        intro H. rewrite IHr. apply le_plus_r.
  Qed.

  Section Search.
    Inductive In (x: nat) : tree nat -> Prop :=
      | InRoot: forall y l r, eq_nat x y -> In x (Node y l r)
      | InLeft: forall y l r, In x l -> In x (Node y l r)
      | InRight: forall y l r, In x r -> In x (Node y l r).

    Definition lt_tree x t := forall y: nat, In y t -> lt y x.
    Definition gt_tree x t := forall y: nat, In y t -> gt y x.

    Lemma lt_leaf: forall x, lt_tree x Leaf.
    Proof. unfold lt_tree. intros. inversion H. Qed.

    Lemma gt_leaf: forall x, gt_tree x Leaf.
    Proof. unfold gt_tree. intros. inversion H. Qed.

    Inductive BST: tree nat -> Prop :=
      | bst_leaf: BST Leaf
      | bst_node: forall x l r,
        BST l -> BST r -> lt_tree x l -> gt_tree x r -> BST (Node x l r).
    Hint Resolve bst_leaf bst_node: bst.

    Fixpoint search (x: nat) (t: tree nat) : option nat :=
      match t with
      | Leaf       => None
      | Node y l r => match nat_compare x y with
        | Lt => search x l
        | Eq => Some y
        | Gt => search x r
      end
    end.

    Fixpoint insert (x: nat) (t: tree nat) : tree nat :=
      match t with
      | Leaf       => Node x Leaf Leaf
      | Node y l r => match nat_compare x y with
        | Lt => Node y (insert x l) r
        | Eq => Node x l r
        | Gt => Node y l (insert x r)
      end
    end.

    Lemma nat_compare_refl: forall n: nat,
      nat_compare n n = Eq.
    Proof.
      intros n. induction n as [| n'].
        reflexivity.
        simpl. apply IHn'.
    Qed.

    Theorem insert_search: forall (x: nat) (t: tree nat),
      search x (insert x t) = Some x.
    Proof.
      intros x t. induction t as [| y l IHl r IHr].
        (* t = Leaf *)
        simpl. rewrite -> nat_compare_refl. reflexivity.
        (* t = Node y l r *)
        simpl. remember (nat_compare x y) as eq. destruct eq.
          (* Eq *) simpl. rewrite nat_compare_refl. reflexivity.
          (* Lt *) simpl. rewrite <- Heqeq. rewrite IHl. reflexivity.
          (* Gt *) simpl. rewrite <- Heqeq. rewrite IHr. reflexivity.
    Qed.

    Theorem insert_correct: forall (x: nat) (t: tree nat),
      BST t -> BST (insert x t).
    Proof.
      intros x t H. induction t as [| y l IHl r IHr].
        simpl.
        apply bst_node.
        auto with bst.
        auto with bst.
        auto with bst.
        apply lt_leaf.
        apply gt_leaf.
        
  End Search.

  Section AVL.
    Open Scope Z_scope.

    Definition balance_factor {X: Type} (t: tree X) : Z :=
      match t with
      | Leaf       => 0
      | Node _ l r => Z.of_nat (tree_height l) - Z.of_nat (tree_height r)
      end.

    Definition is_balanced {X: Type} (t: tree X) : Prop :=
      -1 <= balance_factor t <= 1.

    Inductive AVL {X: Type} : tree X -> Prop :=
      | avl_nil: AVL Leaf
      | avl_node: forall x l r,
        AVL l -> AVL r -> is_balanced l -> is_balanced r -> AVL (Node x l r).
  End AVL.
End Tree.
