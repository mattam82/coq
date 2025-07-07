Set Universe Polymorphism.

Definition relation@{s;u|} (A : 𝒰@{s;u}) := A -> Set.
Axiom fail@{a s;a u|+} : forall {A : 𝒰@{s;u}}, relation@{s;u} (A -> A).

Arguments fail {A}%_type _.

About fail.
