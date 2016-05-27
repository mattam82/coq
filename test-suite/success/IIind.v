(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*- *)

Module separate.
  Universes i j.

  Local Inductive A : Type@{i} :=
    with B : Type@{j} :=.

  Constraint i < j.
End separate.

Module diff.
  Universes k l.

  Local Inductive A : Type@{k} :=
    fooa (a : A) : B -> A
    with B : Type@{l} :=.

  Fail Constraint k < l. (* l <= k due to the constructor *)
End diff.

Module indind.
  Universes m n.

  Local Inductive A : Type@{m} :=
    with B : A -> Type@{n} :=.

  Fail Constraint n < m. (* m <= n due to the indices matter *)
End indind.