Set Universe Polymorphism.
Inductive foo@{s;} : 𝒰@{s;Set} := XX.

Fail Fixpoint bar@{s;} (f:foo@{s;}) : True := I.
