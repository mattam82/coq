Set Printing Universes.  
Module Easy.

  Polymorphic Inductive prod (A : Type) (B : Type) : Type :=
    pair : A -> B -> prod A B.
  
  Check prod nat nat.
  Print Universes.


  Polymorphic Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
  Print sum.
  Check (sum nat nat).

End Easy.


Record hypo : Type := mkhypo {
   hypo_type : Type;
   hypo_proof : hypo_type
 }.

Polymorphic Definition id {A : Type} (a : A) : A := a.

Check (@id Type).


(* Some tests of sort-polymorphisme *)
Section S.
Variable A:Type.
(*
Definition f (B:Type) := (A * B)%type.
*)
Polymorphic Inductive I (B:Type) : Type := prod : A->B->I B.

Check I nat.

End S.
(*
Check f nat nat : Set.
*)
Definition foo:= I nat nat : Set.
Print Universes. Print foo. Set Printing Universes. Print foo.