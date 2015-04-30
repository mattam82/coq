(* -*- mode: coq; coq-prog-args: ("-emacs" "-no-positivity-check") -*- *)

Section Test.

Variable (A : Type).

Inductive T : Type :=
| C : (T -> A) -> T.

Definition funny (x : T)(y : T) : A :=
  match x with 
    | C f => f y
  end.

Definition haha (x : T) : A :=
  funny x x.

Definition a : A := haha (C haha).

End Test.

