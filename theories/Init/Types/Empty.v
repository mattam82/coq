(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(************************************************************************)
(*         *     (see LICENSE file for the text of the license)         *)

Require Import PreludeOptions.
Require Import Notations.
Require Import Typeclasses.

(** listings: empty **)
Inductive empty@{s| |} : Type@{s|0} :=.

(** listings: end **)

Definition empty_rect@{α | u | } : forall (P : empty@{Type|} -> Type@{α | u }) (e : empty), P e
    := fun P e => match e with end.

Notation False := empty@{Prop|}.
Notation SFalse := empty@{SProp|}.

Definition not@{s|u|} (A : Type@{s|u}) := forall (_ : A), empty@{s|}.

Hint Unfold not : core.

Definition False_rect@{s|u|} (P : False -> Type@{s|u}) u : P u := match u with end.

Notation "~ x" := (not x).

Register not as core.not.type.
Register empty as core.False.type.

#[export]
Hint Unfold not: core.


#[projections(primitive=no)]
Class ExFalso@{s s'| l|} (empty : Type@{s|0}) : Type :=
  { ex_falso : forall (P : empty -> Type@{s'|l}) u, P u }.

Instance ExFalso_Prop@{s|l|} : ExFalso@{Prop s | l } empty := {ex_falso P u := match u with end}.

Instance ExFalso_SProp@{s|l|} : ExFalso@{SProp s | l } empty := {ex_falso P u := match u with end}.

Instance ExFalso_Type@{s|l|} : ExFalso@{Type s | l } empty := {ex_falso P u := match u with end}.

Instance ExFalso_mono@{s|l|} : ExFalso@{s s | l } empty := {ex_falso P u := match u with end}.

Fail Instance ExFalso_gen@{s s'|l|} : ExFalso@{s s' | l } empty := {ex_falso P u := match u with end}.
