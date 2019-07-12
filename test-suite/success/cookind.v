Polymorphic Definition f@{i} : Type@{i} := nat.
Polymorphic Definition baz@{i} : Type@{i} -> Type@{i} := fun x => x.

Section Foo.
  Universe u.
  Context (A : Type@{u}).

  Inductive Bar :=
  | bar : A -> Bar.

  Set Universe Minimization ToSet.
  Inductive Baz :=
  | cbaz : A -> baz Baz -> Baz.

  Inductive Baz' :=
  | cbaz' : A -> baz@{Set} nat -> Baz'.

  (* 2 constructors, at least in Set *)
  Inductive Bazset@{v} :=
  | cbaz1 : A -> baz@{v} Bazset -> Bazset
  | cbaz2 : Bazset.

  Eval compute in ltac:(let T := type of A in exact T).

  Inductive Foo : Type :=
  | foo : A -> f -> Foo.

End Foo.

Set Printing Universes.
(* Cannot fall back to Prop or Set anymore as baz is no longer template-polymorphic *)
Fail Check Bar True : Prop.
Fail Check Bar nat : Set.
About Baz.

Check cbaz True I.

(** Neither caxn it be Set *)
Fail Check Baz nat : Set.

(** No longer possible for Baz' which contains a type in Set *)
Fail Check Baz' True : Prop.
Fail Check Baz' nat : Set.

Fail Check Bazset True : Prop.
Fail Check Bazset True : Set.

(** We can force the universe instantiated in [baz Bazset] to be [u], so Bazset lives in max(Set, u). *)
Constraint u = Bazset.v.
(** As u is global it is already > Set, so: *)
Definition bazsetex@{i | i < u} : Type@{u} := Bazset Type@{i}.

(* Bazset is closed for universes u = u0, cannot be instantiated with Prop *)
Definition bazseetpar (X : Type@{u}) : Type@{u} := Bazset X.

(** Would otherwise break singleton elimination and extraction. *)
Fail Check Foo True : Prop.
Fail Check Foo True : Set.

Definition foo_proj {A} (f : Foo A) : nat :=
  match f with foo _ _ n => n end.

Definition ex : Foo True := foo _ I 0.
Check foo_proj ex.
