#[universes(cumulative)]
Polymorphic Inductive eq@{s s';l +|} {A:𝒰@{s;l}} (x:A) : A -> 𝒰@{s';_} :=
  eq_refl : eq x x.

Check eq 0 0 : SProp.
Check eq 0 0 : Prop.
