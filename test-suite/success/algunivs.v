Universes i j k l.


Constraint i <= j, j <= k, k <= l.

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

Definition typesigstruct := @sigma@{i+1 max(i,j+1)} Type@{i} (fun T => typestruct@{i j} T).


Check (unit -> unit).
