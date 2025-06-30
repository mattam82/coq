

Class Foo (A : Type).
Class Foo2 (A : Type).
Class Bar (A : Type).
Class Baz (A : Type).
(* Instance foo_bar A : Foo A -> Bar A := {}. *)

Instance foo_opt A : Foo (option A) := {}.
Set Typeclasses Debug Verbosity 2.

Definition foo := _ : Foo (option (option nat)).
Fail Definition foo' := _ : Bar (option (option nat)).

Instance: Foo nat := {}.
Instance: Foo bool := {}.
Instance: Foo2 nat := {}.

Instance branch {A} : Foo A -> Foo2 A -> Bar A := {}.
Instance deep {A} : Bar A -> Bar A -> Baz A := {}.

Class NoInst (A : Type).

Instance failing A : NoInst A -> Baz A := {}.
Check _ : Baz _.

