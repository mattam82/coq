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

Section UnitPoly.
  Sort s.
  Inductive unit : Type@{s|Set} :=
      tt : unit.

End UnitPoly.

Notation True := unit@{Prop|}.

Register unit as core.unit.type.
Register tt as core.unit.tt.
