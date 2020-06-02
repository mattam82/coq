(* -*- coq-prog-args: ("-emacs" "-indices-matter") -*- *)
Inductive C (A : Type) : Set :=
with equiv (A : Type) : C A -> Type :=.

Check eq_refl : ltac:(let t := type of equiv in exact t) = (forall A, C A -> Set).