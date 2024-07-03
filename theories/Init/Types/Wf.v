(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * This module proves the validity of
    - well-founded recursion (also known as course of values)
    - well-founded induction
    from a well-founded ordering on a given set *)

Require Import PreludeOptions.
Require Import Notations.

(** Well-founded induction principle on [Prop] *)

Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)
 (** (Acc_rect is automatically defined because Acc is a singleton type) *)

 Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

 Register Acc as core.wf.acc.

 Definition Acc_inv (x:A) (a : Acc x) : forall (y:A), R y x -> Acc y := match a with Acc_intro _ f => f end.

 Global Arguments Acc_inv [x] _ [y] _, [x] _ y _.
 Register Acc_inv as core.wf.acc_inv.

 (** A relation is well-founded if every element is accessible *)

 Definition well_founded := forall a:A, Acc a.

 Register well_founded as core.wf.well_founded.

 (** Well-founded induction on [Set] and [Prop] *)
End Well_founded.
