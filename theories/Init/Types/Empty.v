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

(** listings: empty **)
Inductive empty@{s| |} : Type@{s|0} :=.
(** listings: end **)

Notation False := empty@{Prop|}.
Notation SFalse := empty@{SProp|}.

Definition not@{s|u|} (A : Type@{s|u}) := forall (_ : A), empty@{s|}.

Definition False_rect@{s|u|} (P : False -> Type@{s|u}) u : P u := match u with end.

Notation "~ x" := (not x).

Register not as core.not.type.
Register empty as core.False.type.
