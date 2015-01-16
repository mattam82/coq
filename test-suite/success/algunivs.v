Universes i j k l. 
Print Universes.
Constraint i <= j, j <= k, j <= l.

Constraint i = k.

Constraint i + 1 = j.

Universes l.

Constraint i <= j. 
Print Universes.

Constraint j <= l, k <= l.

Print Universes.
Constraint i <= j, j <= k.

Print Universes.

Constraint i + 1 = j.
Print Universes.
(*
Top.3  <= Top.4
Top.2 = Top.1+1
Top.1 + 1 <= Top.3
       <= Top.2
Prop + 1 <= Set*)

Fail Constraint j = i.
(* Constraint j = k. *)
(* Print Universes. *)

Constraint i < j.
Print Universes.

Constraint i <= i.
Print Universes.

Constraint j <= j.
Print Universes.

Constraint j <= i + 1.
Print Universes.

Constraint j = i + 1.
Print Universes.

Constraint k = i + 2.
Print Universes.

Constraint k = j + 1.
Print Universes.

Fail Constraint k = j. (* Bad message *)
Print Universes.

Fail Constraint k = j. (* Bad message *)
Print Universes.

Universe u.
Definition Type0 := Type@{u}.
Definition Type1 := Type@{u+1}.
Definition Type2 := Type@{u+2}.

Constraint u < u+1.


Parameter A : Type0.

Check A : Type1.
Check A : Type2.
Check A : Type.
Check A : Type1.

Polymorphic Definition foo (A : Type@{i}) : Type@{i} := A.

Definition bar := foo A : Type0.

Constraint u = i.

Polymorphic Definition foo2 (A : Type) := A.
Check foo2 A.
Fail Check foo2@{j} A : Type@{u}. (* False *)
(* Definition baz := foo2@{j} A : Type@{u}. *)
Print Universes.

Polymorphic Record sigma (A : Type) (B : forall x : A, Type) := 
  pair { fst : A ; snd : B fst }.

Polymorphic Inductive typestruct (A : Type) := 
  { hom : A -> A -> Type }.

Definition typesig := @sigma Type (fun T => T).

Polymorphic Definition typesigstruct := @sigma Type (fun T => typestruct T).

Polymorphic Definition projtypestruct (x : typesigstruct) := fst _ _ x.

Universes L uni H.
Constraint L < uni, uni < H.

Constraint L < H.

Constraint uni = L+1.

Polymorphic Definition leq (A : Type@{u0}) : Type@{u1} := A.

Polymorphic Definition foo' (A : Type@{u0}) (B : leq@{u0 u1} A) := B.

Polymorphic Definition three (A : Type@{u0}) (B : leq@{u0 u1} A) (C : leq@{u1 u2} A) := C.
Polymorphic Definition leq2 (A : Type@{u0}) (B : Type@{u1}) : Type@{u2} := (A * B)%type.

Check three@{v max(v) x}.
Check three@{v w+1 max(v,v+1)}.
Check three@{v w+1 max(v,v+1)}.
Definition bar' (A : Type@{x}) (B : Type@{y}) := leq2@{x y max(x,y)}.

Check (unit -> unit).

Universes x y z.

Constraint x < z.

Constraint x + 1 <= y.

Constraint x + 1 <= y.

Polymorphic Definition twice {A : Type} (x y : A) := A.

Check twice Type@{v} Type@{v}.

Check twice Type@{v} Type@{w}.

Check twice Type@{v+1} Type@{w}.

Check twice Type@{max(v+1,v2)} Type@{w}.

Universe U0 U1 U2 U3.

Constraint U0+1 <= U1.
Constraint U1 <= U2.
Constraint U2 <= U3.

Polymorphic Definition check_smaller (a : Type@{v}) : Type@{w} := a.

Check check_smaller Type@{U0} : Type@{U3}.

Constraint U0 <= U3.
Constraint U0+1 <= U3.
Constraint U0+2 <= U3.

Constraint U0+1 <= U3.

