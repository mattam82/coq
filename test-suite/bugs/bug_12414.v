Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.
Inductive list@{s|l|} {T : Type@{s|l}} : Type@{s | l} := | cons (t : T) : list -> list. (* who needs nil anyway? *)
Arguments list : clear implicits.
Section map.
  Sort s.
  Context {A B : Type@{s|_}}.
  Fixpoint map (f: A -> B) (l : list A) : list B :=
  let '(cons t l) := l in cons (f t) (map f l).
End map.
Check map@{Type|_ _}.
(* Two universes, as expected. *)

Definition map_Set@{} {A B : Set} := @map A B.
Definition map_Prop@{} {A B : Prop} := @map A B.
