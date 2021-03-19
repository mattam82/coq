From Coq Require Import Setoid.

Lemma test {A}
      (lookup : list A -> nat -> option A)
      (opA : option A -> option A -> option A)
      (opL : list A -> list A -> list A)
      (val : option A -> Prop) :
   (forall l1 l2 (i : nat), lookup (opL l1 l2) i = opA (lookup l1 i) (lookup l2 i)) ->
   forall l1 l2, (forall i : nat, val (lookup (opL l1 l2) i)) -> forall i : nat, val (lookup l1 i).
Proof.
  intros list_lookup_op l1 l2.
  (* setoid_rewrite list_lookup_op. Undo. *)
Hint Mode Reflexive ! ! : typeclass_instances.

  setoid_rewrite list_lookup_op.
Abort.
