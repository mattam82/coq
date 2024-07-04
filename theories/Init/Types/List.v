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
Require Import Types.Nat.

Inductive list@{s|u|} (A : Type@{s|u}) : Type@{s|u} :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

Declare Scope list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Infix "::" := cons (at level 60, right associativity) : list_scope.

Register list as core.list.type.
Register nil as core.list.nil.
Register cons as core.list.cons.

Section ListPolyDefinitions.
  Sort s.
  Universe u.

  Local Open Scope list_scope.

  Definition length (A : Type@{s|u}) : list A -> nat@{s|} :=
    fix length l :=
    match l with
    | nil => O
    | _ :: l' => S (length l')
    end.

(** Concatenation of two lists *)

  Definition app (A : Type@{s|u}) : list A -> list A -> list A :=
    fix app l m :=
    match l with
    | nil => m
    | a :: l1 => a :: app l1 m
    end.

End ListPolyDefinitions.

Arguments app {A} l m.

Infix "++" := app (right associativity, at level 60) : list_scope.
