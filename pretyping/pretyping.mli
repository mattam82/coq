(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file implements type inference. It maps [glob_constr]
   (i.e. untyped terms whose names are located) to [constr]. In
   particular, it drives complex pattern-matching problems ("match")
   into elementary ones, insertion of coercions and resolution of
   implicit arguments. *)

open Names
open Context
open Term
open Environ
open Evd
open Glob_term
open Evarutil
open Misctypes

(** An auxiliary function for searching for fixpoint guard indexes *)

val search_guard :
  Loc.t -> env -> int list list -> rec_declaration -> int array

type typing_constraint = OfType of types | IsType | WithoutTypeConstraint

type var_map = Pattern.constr_under_binders Id.Map.t
type unbound_ltac_var_map = Genarg.tlevel Genarg.generic_argument Id.Map.t
type ltac_var_map = var_map * unbound_ltac_var_map
type glob_constr_ltac_closure = ltac_var_map * glob_constr
type pure_open_constr = evar_map * constr

type inference_flags = {
  use_typeclasses : bool;
  use_unif_heuristics : bool;
  use_hook : (env -> evar_map -> evar -> constr) option;
  fail_evar : bool;
  expand_evars : bool
}

val default_inference_flags : bool -> inference_flags

val no_classes_no_fail_inference_flags : inference_flags

val all_no_fail_flags : inference_flags

val all_and_fail_flags : inference_flags

(** Allow references to syntaxically inexistent variables (i.e., if applied on an inductive) *)
val allow_anonymous_refs : bool ref
  
(** Generic call to the interpreter from glob_constr to open_constr, leaving
    unresolved holes as evars and returning the typing contexts of
    these evars. Work as [understand_gen] for the rest. *)

val understand_tcc : ?flags:inference_flags -> evar_map -> env ->
  ?expected_type:typing_constraint -> glob_constr -> open_constr

val understand_tcc_evars : ?flags:inference_flags -> evar_map ref -> env ->
  ?expected_type:typing_constraint -> glob_constr -> constr

(** More general entry point with evars from ltac *)

(** Generic call to the interpreter from glob_constr to constr

    In [understand_ltac flags sigma env ltac_env constraint c],

    flags: tell how to manage evars
    sigma: initial set of existential variables (typically current goals)
    ltac_env: partial substitution of variables (used for the tactic language)
    constraint: tell if interpreted as a possibly constrained term or a type
*)

val understand_ltac : inference_flags ->
  evar_map -> env -> ltac_var_map ->
  typing_constraint -> glob_constr -> pure_open_constr

(** Standard call to get a constr from a glob_constr, resolving implicit args *)

val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
  evar_map -> env -> glob_constr -> constr Univ.in_universe_context_set

(** Idem but returns the judgment of the understood term *)

val understand_judgment : evar_map -> env -> 
  glob_constr -> unsafe_judgment Evd.in_evar_universe_context

(** Idem but do not fail on unresolved evars *)
val understand_judgment_tcc : evar_map ref -> env -> 
  glob_constr -> unsafe_judgment

(** Trying to solve remaining evars and remaining conversion problems
    with type classes, heuristics, and possibly an external solver *)

val solve_remaining_evars : inference_flags ->
  env -> (* initial map *) evar_map -> (* map to solve *) evar_map -> evar_map

(** Checking evars are all solved and reporting an appropriate error message *)

val check_evars_are_solved :
  env -> (* initial map: *) evar_map -> (* map to check: *) evar_map -> unit

(**/**)
(** Internal of Pretyping... *)
val pretype :
  type_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_judgment

val pretype_type :
  val_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_type_judgment

val ise_pretype_gen :
  inference_flags -> evar_map -> env ->
  ltac_var_map -> typing_constraint -> glob_constr -> evar_map * constr

(**/**)

(** To embed constr in glob_constr *)

val constr_in : constr -> Dyn.t
val constr_out : Dyn.t -> constr

val interp_sort : evar_map -> glob_sort -> evar_map * sorts
val interp_elimination_sort : glob_sort -> sorts_family
