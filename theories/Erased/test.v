Definition nate := nat@{Erased|}.

Fail Fixpoint id (n : nate) : nat@{Type|} :=
  match n return nat@{Type|} with
  | O => O
  | S n => S (id n)
  end.

Fixpoint ide (n : nate) : nate :=
  match n with
  | O => O
  | S n => S (ide n)
  end.

Definition large_elim (b : bool@{Erased|}) : Prop :=
  if b then True else False.

Lemma true_neq_false : true@{Erased|} <> false@{Erased|}.
Proof.
  intro e.
  change (large_elim false).
  destruct e.
  cbn.
  exact tt.
Qed.
