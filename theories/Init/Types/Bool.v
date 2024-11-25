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

(** listings: bool **)
Inductive bool@{s| |} : Type@{s|0} :=
  | true : bool
  | false : bool.
(** listings: end **)

Add Printing If bool.

Register bool as core.bool.type.
Register true as core.bool.true.
Register false as core.bool.false.

Definition eqb@{s| |} (b1 b2 : bool@{s|}) : bool@{s|} :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition negb@{s| |} (a : bool@{s|}) : bool@{s|} :=
  match a with
    | true => false
    | false => true
  end.

Definition andb@{s| |} (a b : bool@{s|}) : bool@{s|} :=
  match a with
    | true => b
    | false => false
  end.

Definition orb@{s| |} (a b : bool@{s|}) : bool@{s|} :=
  match a with
    | true => true
    | false => b
  end.

Definition implb@{s| |} (a b : bool@{s|}) := orb (negb a) b.

Definition xorb@{s| |} (a b : bool@{s|}) :=
  match a with
    | true => negb b
    | false => b
  end.

Register eqb as core.bool.eqb.
Register andb as core.bool.andb.
Register orb as core.bool.orb.
Register implb as core.bool.implb.
Register xorb as core.bool.xorb.
Register negb as core.bool.negb.

Declare Scope bool_scope.
Delimit Scope bool_scope with bool.
Bind Scope bool_scope with bool.


Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.
