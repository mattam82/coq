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

Section EmptySortPoly.
  Sort s.

  Inductive Empty : Type@{s|Set} :=.

  Scheme Empty_poly := Induction for Empty Sort Poly.

  Definition not (A : Type@{s|Set}) := forall (_ : A), Empty.
End EmptySortPoly.

Definition False_rect@{s|u|} (P : Empty@{Prop|} -> Type@{s|u}) u : P u := match u with end.

Notation "~ x" := (not x).

Register not as core.not.type.
