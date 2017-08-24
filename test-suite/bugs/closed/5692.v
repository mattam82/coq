Set Primitive Projections.

Module noparam.

Structure semigroup := SemiGroup {
  sg_car :> Type;
  sg_op : sg_car -> sg_car -> sg_car;
}.

Structure monoid := Monoid {
  monoid_car :> Type;
  monoid_op : monoid_car -> monoid_car -> monoid_car;
  monoid_unit : monoid_car;
  monoid_left_id x : monoid_op monoid_unit x = x;
}.

Coercion monoid_sg (X : monoid) : semigroup :=
  SemiGroup (monoid_car X) (monoid_op X).
Canonical Structure monoid_sg.

Canonical Structure nat_sg := SemiGroup nat plus.
Canonical Structure nat_monoid := Monoid nat plus 0 plus_O_n.

Module bug1.

Parameter X : monoid.
Parameter x y : X.

Check (sg_op _ x y).
End bug1.

(*
Error: The term "x" has type "monoid_car X" while it is expected to have type "sg_car ?s".
*)

Lemma foo (x : nat) : 0 + x = x.
Proof.
  apply monoid_left_id.
Qed.
(*
The command has indeed failed with message:
In environment
x : nat
Unable to unify
 "@eq (monoid_car ?M158) (monoid_op ?M158 (monoid_unit ?M158) ?M159) ?M159"
with "@eq nat (Nat.add O x) x".
 *)

End noparam.

Module withparam.

Structure semigroup := SemiGroup {
  sg_car :> Type;
  sg_op : sg_car -> sg_car -> sg_car;
}.

Structure monoid (monoid_car : Type) := Monoid {
  monoid_op : monoid_car -> monoid_car -> monoid_car;
  monoid_unit : monoid_car;
  monoid_left_id x : monoid_op monoid_unit x = x;
}.

Coercion monoid_sg {A} (X : monoid A) : semigroup :=
  SemiGroup A (monoid_op A X).
Canonical Structure monoid_sg.

Canonical Structure nat_sg := SemiGroup nat plus.
Canonical Structure nat_monoid := Monoid nat plus 0 plus_O_n.

Module bug1.
Parameter A : Type.
Parameter X : monoid A.
Parameter x y : X.

Check (sg_op _ x y).
End bug1.

(*
Error: The term "x" has type "monoid_car X" while it is expected to have type "sg_car ?s".
*)

Lemma foo (x : nat) : 0 + x = x.
Proof.
  apply monoid_left_id.
Qed.
(*
The command has indeed failed with message:
In environment
x : nat
Unable to unify
 "@eq (monoid_car ?M158) (monoid_op ?M158 (monoid_unit ?M158) ?M159) ?M159"
with "@eq nat (Nat.add O x) x".
 *)
End withparam.