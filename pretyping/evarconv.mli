(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Reductionops
open Evd
open Locus

(** {4 Unification for type inference. } *)

type unify_flags = {
  open_ts : transparent_state;
  closed_ts : transparent_state;
  frozen_evars : Evar.Set.t;
  allow_K_at_toplevel : bool;
  with_cs : bool }

val default_flags_of : transparent_state -> unify_flags

type unify_fun = unify_flags ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result

val conv_fun : unify_fun -> unify_flags -> Evarsolve.conv_fun

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** {6 Main unification algorithm for type inference. } *)

(** returns exception UnableToUnify with best known evar_map if not unifiable *)
val the_conv_x     : env -> ?ts:transparent_state -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : env -> ?ts:transparent_state -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : env -> ?ts:transparent_state -> evar_map ref -> constr -> constr -> bool
val e_cumul : env -> ?ts:transparent_state -> evar_map ref -> constr -> constr -> bool

(** {6 Unification heuristics. } *)

(** Try heuristics to solve pending unification problems and to solve
    evars with candidates *)

val consider_remaining_unif_problems :
  env -> ?flags:unify_flags -> ?with_ho:bool -> evar_map -> evar_map

(** Check all pending unification problems are solved and raise an
    error otherwise *)

val check_problems_are_solved : env -> evar_map -> unit

(** Check if a canonical structure is applicable *)

val check_conv_record : env -> evar_map -> 
  constr * types Stack.t -> constr * types Stack.t ->
  Univ.universe_context_set * (constr * constr) 
  * constr * constr list * (constr Stack.t * constr Stack.t) *
    (constr Stack.t * types Stack.t) *
    (constr Stack.t * types Stack.t) * constr *
    (int option * constr)

(** Try to solve problems of the form ?x[args] = c by second-order
    matching, using typing to select occurrences *)

type occurrence_match_test =
  env -> evar_map -> constr -> (* Used to precompute the local tests *)
  env -> evar_map -> int -> constr -> constr -> bool * evar_map

(** When given the choice of abstracting an occurrence or leaving it,
    force abstration. *)
type prefer_abstraction = bool

type occurrence_selection =
  | AtOccurrences of occurrences
  | Unspecified of prefer_abstraction

(** By default, unspecified, not preferring abstraction.
    This provides the most general solutions. *)
val default_occurrence_selection : occurrence_selection

type occurrences_selection =
  occurrence_match_test * occurrence_selection list

val default_occurrence_test : occurrence_match_test

(** [default_occurrence_selection n]
    Gives the default test and occurrences for [n] arguments *)
val default_occurrences_selection : int -> occurrences_selection

val second_order_matching : unify_flags -> env -> evar_map ->
  existential -> occurrences_selection -> constr -> evar_map * bool

(** Declare function to enforce evars resolution by using typing constraints *)

val set_solve_evars : (env -> evar_map ref -> constr -> constr) -> unit

(** Override default [evar_conv_x] algorithm. *)
val set_evar_conv : unify_fun -> unit

(** The default unification algorithm with evars and universes. *)
val evar_conv_x : unify_fun

(**/**)
(* For debugging *)
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> unify_flags ->
  env -> evar_map ->
    conv_pb -> state * Cst_stack.t -> state * Cst_stack.t ->
      Evarsolve.unification_result

val apply_on_subterm :
             Environ.env ->
           Evd.evar_map ref ->
           Evar.Set.t ->
           Evar.Set.t ref ->
           (int -> Term.types -> Term.constr) ->
           (Environ.env ->
            Evd.evar_map ->
            Constr.constr ->
            Environ.env ->
            Evd.evar_map ->
            int -> Constr.constr -> Term.types -> bool * Evd.evar_map) ->
           Constr.constr -> Term.constr -> Term.constr

(**/**)

