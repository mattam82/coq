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

Section ListPoly.
  Sort s.
  Universe u.

  Inductive list (A : Type@{s|u}) : Type@{s|u} :=
   | nil : list A
   | cons : A -> list A -> list A.

  Arguments nil {A}.
  Arguments cons {A} a l.
End ListPoly.

Declare Scope list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Infix "::" := cons (at level 60, right associativity) : list_scope.

Register list as core.list.type.
Register nil as core.list.nil.
Register cons as core.list.cons.
