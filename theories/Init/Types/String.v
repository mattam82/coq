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
Require Import Types.Ascii Types.Bool.

Inductive string@{s| |} : Type@{s|0} :=
| EmptyString : string
| String : ascii@{s|} -> string -> string.

Fixpoint eqb@{s| |} (s1 s2 : string@{s|}) : bool@{s|} :=
    match s1, s2 with
    | EmptyString, EmptyString => true
    | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 && eqb s1' s2'
    | _,_ => false
    end.

Declare Scope string_scope.
Delimit Scope string_scope with string.
Bind Scope string_scope with string.

Register string as core.string.type.
Register EmptyString as core.string.empty.
Register String as core.string.string.
