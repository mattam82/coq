(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Univ
open Environ
open Declarations
open Entries

val translate_local_def : env -> constr * types option ->
  constr * types * universe_context_set

val translate_local_assum : env -> types ->
  types * universe_context_set

val infer_declaration : env -> constant_entry ->
  constant_def * constant_type * bool * universe_context * bool * Sign.section_context option

val translate_constant : env -> constant -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> constant -> Cooking.recipe -> constant_body


(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : env -> constant_entry -> Cooking.result
val build_constant_declaration : env -> constant -> Cooking.result -> constant_body
