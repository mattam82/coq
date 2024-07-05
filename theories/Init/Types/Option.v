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

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option@{s s'|u|} (A:Type@{s|u}) : Type@{s'|u} :=
  | Some : A -> option A
  | None : option A.

Arguments Some {A} a.
Arguments None {A}.

Register option as core.option.type.
Register Some as core.option.Some.
Register None as core.option.None.

Definition option_map@{s s'|u v|} {A : Type@{s|u}} {B:Type@{s|v}} (f:A->B) (o : option@{_ s'|_} A) : option@{_ s'|_} B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end.
