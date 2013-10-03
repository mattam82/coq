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

val translate_local_def : env -> definition_entry ->
  constr * types

val translate_local_assum : env -> types -> types

val translate_constant : env -> kernel_name -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> kernel_name -> Cooking.recipe -> constant_body


(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : env -> kernel_name -> constant_entry -> Cooking.result
val build_constant_declaration : env -> kernel_name -> Cooking.result -> constant_body
