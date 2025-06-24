Set Universe Polymorphism.
Inductive foo@{s;} : 𝒰@{s;0} := XX.

Fail Fixpoint bar@{s;} (f:foo@{s;}) : True := I.
