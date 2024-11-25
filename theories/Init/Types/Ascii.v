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
Require Import Types.Bool.

Inductive ascii@{s| |} : Type@{s|0} := Ascii (_ _ _ _ _ _ _ _ : bool@{s|}).

Definition eqb@{s| |} (a b : ascii@{s|}) : bool@{s|} :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3
    && Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
 end.

Declare Scope char_scope.
Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Register ascii as core.ascii.type.
Register Ascii as core.ascii.ascii.
