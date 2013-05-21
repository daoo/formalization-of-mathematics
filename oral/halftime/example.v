Inductive bool := false | true.

Definition negb (b: bool) :=
  match b with
  | false => true
  | true  => false
  end.

Theorem negb_involutive: forall (b: bool),
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.
Qed.