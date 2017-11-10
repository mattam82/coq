(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ
open Declarations
open Environ
open Names
val check_subtypes : env -> module_type_body -> module_type_body -> constraints

type namedobject =
  | Constant of constant_body
  | IndType of inductive * mutual_inductive_body
  | IndConstr of constructor * mutual_inductive_body

type namedmodule =
  | Module of module_body
  | Modtype of module_type_body

val check_constant :            Univ.Constraint.t ->
           Environ.env ->
           'a ->
           Names.Label.t ->
           namedobject ->
           Declarations.constant_body ->
           Declarations.structure_field_body ->
           Mod_subst.substitution ->
           Mod_subst.substitution -> Univ.Constraint.t

val check_conv_error :            (Modops.signature_mismatch_error -> Univ.Constraint.t) ->
           Modops.signature_mismatch_error ->
           Univ.Constraint.t ->
           bool ->
           (Environ.env ->
            UGraph.t -> Term.types -> Term.types -> Univ.Constraint.t) ->
           Environ.env -> Term.types -> Term.types -> Univ.Constraint.t
