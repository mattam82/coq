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

Section EmptySortPoly.
  Sort s.

  Inductive empty : Type@{s|Set} :=.

  Scheme empty_poly := Induction for empty Sort Poly.

  About empty_poly.

  Definition not (A : Type@{s|Set}) := forall (_ : A), empty.
End EmptySortPoly.
