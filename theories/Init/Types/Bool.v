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

Section BoolSortPoly.
  Sort s.

  Inductive bool : Type@{s|Set} :=
    | true : bool
    | false : bool.

  Scheme bool_poly := Induction for bool Sort Poly.

  Add Printing If bool.

  Declare Scope bool_scope.
  Delimit Scope bool_scope with bool.
  Bind Scope bool_scope with bool.

  Register bool as core.bool.type.
  Register true as core.bool.true.
  Register false as core.bool.false.


  Definition negb (a : bool) : bool :=
    match a with
      | true => false
      | false => true
    end.

  Definition andb (a b : bool) : bool :=
    match a with
      | true => b
      | false => false
    end.

  Definition orb (a b : bool) : bool :=
    match a with
      | true => true
      | false => b
    end.

  Definition implb (a b : bool) := orb (negb a) b.

  Definition xorb (a b : bool) :=
    match a with
      | true => negb b
      | false => b
    end.

  Infix "||" := orb : bool_scope.
  Infix "&&" := andb : bool_scope.

  Register andb as core.bool.andb.
  Register orb as core.bool.orb.
  Register implb as core.bool.implb.
  Register xorb as core.bool.xorb.
  Register negb as core.bool.negb.

End BoolSortPoly.
