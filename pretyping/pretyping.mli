(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Sign
open Term
open Environ
open Evd
open Glob_term
open Evarutil

(** An auxiliary function for searching for fixpoint guard indexes *)

val search_guard :
  Pp.loc -> env -> int list list -> rec_declaration -> int array

type typing_constraint = OfType of types option | IsType

type var_map = (identifier * Pattern.constr_under_binders) list
type unbound_ltac_var_map = (identifier * identifier option) list
type ltac_var_map = var_map * unbound_ltac_var_map
type glob_constr_ltac_closure = ltac_var_map * glob_constr
type pure_open_constr = evar_map * constr

(** Allow references to syntaxically inexistent variables (i.e., if applied on an inductive) *)
val allow_anonymous_refs : bool ref
  
(** Generic call to the interpreter from glob_constr to open_constr, leaving
    unresolved holes as evars and returning the typing contexts of
    these evars. Work as [understand_gen] for the rest. *)

val understand_tcc : ?resolve_classes:bool ->
  evar_map -> env -> ?expected_type:types -> glob_constr -> open_constr  * relevance

val understand_tcc_evars : ?fail_evar:bool -> ?resolve_classes:bool ->
  evar_map ref -> env -> typing_constraint -> glob_constr -> constr * relevance

(** More general entry point with evars from ltac *)

(** Generic call to the interpreter from glob_constr to constr, failing
    unresolved holes in the glob_constr cannot be instantiated.

    In [understand_ltac expand_evars sigma env ltac_env constraint c],

    expand_evars : expand inferred evars by their value if any
    sigma : initial set of existential variables (typically dependent subgoals)
    ltac_env : partial substitution of variables (used for the tactic language)
    constraint : tell if interpreted as a possibly constrained term or a type
*)

val understand_ltac : ?resolve_classes:bool ->
  bool -> evar_map -> env -> ltac_var_map ->
  typing_constraint -> glob_constr -> pure_open_constr

(** Standard call to get a constr from a glob_constr, resolving implicit args *)

val understand : evar_map -> env -> ?expected_type:Term.types ->
  glob_constr -> constr

(** Idem but the glob_constr is intended to be a type *)

val understand_type : evar_map -> env -> glob_constr -> constr * relevance

(** A generalization of the two previous case *)

val understand_gen : typing_constraint -> evar_map -> env ->
  glob_constr -> constr * relevance

(** Idem but returns the judgment of the understood term *)

val understand_judgment : evar_map -> env -> glob_constr -> 
  unsafe_judgment * relevance

(** Idem but do not fail on unresolved evars *)
val understand_judgment_tcc : evar_map ref -> env -> glob_constr -> 
  unsafe_judgment * relevance

(**/**)
(** Internal of Pretyping... *)
val pretype :
  type_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_judgment * relevance

val pretype_type :
  val_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_type_judgment * relevance

val pretype_gen :
  bool -> bool -> bool -> evar_map ref -> env ->
  ltac_var_map -> typing_constraint -> glob_constr -> constr * relevance

(**/**)

(** To embed constr in glob_constr *)

val constr_in : constr -> Dyn.t
val constr_out : Dyn.t -> constr

val interp_sort : glob_sort -> sorts
val interp_elimination_sort : glob_sort -> sorts_family

(** Last chance for solving evars, possibly using external solver *)
val solve_remaining_evars : bool -> bool ->
  (env -> evar_map -> existential -> constr) ->
  env -> evar_map -> pure_open_constr -> pure_open_constr
