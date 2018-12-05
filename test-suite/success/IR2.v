
Require Import IR.

Import SetUniv.

Print Impls.bete.

Definition foo := IR.Impls.rec.

Definition foo' := IR.SetUniv.El.

Eval compute in foo.

Eval compute in foo'.


Definition bar := El cunit.

Eval compute in bar.

Eval compute in F.