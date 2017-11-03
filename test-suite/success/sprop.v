
Definition iUnit : SProp := forall A : SProp, A -> A.

Definition itt : iUnit := fun A a => a.

Definition iUnit_irr (P : iUnit -> Type) (x y : iUnit) : P x -> P y
  := fun v => v.

Inductive sBox (A:SProp) : Prop := sbox : A -> sBox A.

Definition uBox := sBox iUnit.

Definition sBox_irr A (x y : sBox A) : x = y.
Proof.
  destruct x as [x], y as [y].
  reflexivity.
Defined.

Set Primitive Projections.
(* Primitive record with all fields in SProp has the eta property of SProp so must be SProp. *)
Record rBox (A:SProp) : Prop := { relem : A }.

(* putting nonempty inductives in SProp doesn't yet work :p *)

Inductive sEmpty : SProp := .

Fail Inductive sUnit : SProp := stt.
