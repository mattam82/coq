(** Extraction to Haskell : use of basic Haskell types *)

Require Corelib.extraction.Extraction.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" [ "([])" "(:)" ].
Extract Inductive sigmaR => "(,)" [ "(,)" ].

(* **Fixme** we should be able to specify extraction based on the sort instantiation *)

(*Extract Inductive sum => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sum => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].*)
Extract Inductive sum => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".
