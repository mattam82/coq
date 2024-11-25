(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Notations.

Inductive sum@{s s' s''|u v|} (A : Type@{s|u}) (B : Type@{s'|v}) : Type@{s''|max(u,v)} :=
  | left : A -> sum A B
  | right : B -> sum A B.

Arguments left {_}.
Arguments right _ {_}.

Notation "{ A } + { B }" := (sum A B).

Notation "A \/ B" := (sum@{Prop Prop Prop|_ _} A B).
