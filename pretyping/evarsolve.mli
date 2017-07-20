(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Evd
open Environ

type unify_flags = {
  open_ts : Names.transparent_state;
  closed_ts : Names.transparent_state;
  subterm_ts : Names.transparent_state;
  frozen_evars : Evar.Set.t;
  allow_K_at_toplevel : bool;
  with_cs : bool }

type unification_result =
  | Success of evar_map
  | UnifFailure of evar_map * Pretype_errors.unification_error

val is_success : unification_result -> bool

(** Replace the vars and rels that are aliases to other vars and rels by 
   their representative that is most ancient in the context *)
val expand_vars_in_term : env -> constr -> constr

(** [evar_define choose env ev c] try to instantiate [ev] with [c] (typed in [env]),
   possibly solving related unification problems, possibly leaving open
   some problems that cannot be solved in a unique way (except if choose is
   true); fails if the instance is not valid for the given [ev] *)

type types_or_terms = bool

type conv_fun = types_or_terms ->
  env -> evar_map -> conv_pb -> constr -> constr -> unification_result

type conv_fun_bool = types_or_terms ->
  env ->  evar_map -> conv_pb -> constr -> constr -> bool

val evar_define : unify_flags -> conv_fun -> ?choose:bool -> ?imitate_defs:bool ->
  env -> evar_map -> bool option -> existential -> constr -> evar_map

val refresh_universes :
  ?status:Evd.rigid ->
  ?onlyalg:bool (* Only algebraic universes *) ->
  ?refreshset:bool ->
  (* Also refresh Prop and Set universes, so that the returned type can be any supertype
     of the original type *)
  bool option (* direction: true for levels lower than the existing levels *) ->
  env -> evar_map -> types -> evar_map * types

val solve_refl : ?can_drop:bool -> unify_flags -> conv_fun_bool -> env ->  evar_map ->
  bool option -> existential_key -> constr array -> constr array -> evar_map

val solve_evar_evar : ?force:bool -> unify_flags ->
  (env -> evar_map -> bool option -> existential -> constr -> evar_map) ->
  conv_fun ->
  env ->  evar_map -> bool option -> existential -> existential -> evar_map

val solve_simple_eqn : unify_flags -> conv_fun -> ?choose:bool -> ?imitate_defs:bool -> env ->  evar_map ->
  bool option * existential * constr -> unification_result

val reconsider_conv_pbs : conv_fun -> evar_map -> unification_result

val is_unification_pattern_evar : env -> evar_map -> existential -> constr list ->
  constr -> constr list option

val is_unification_pattern : env * int -> evar_map -> constr -> constr list ->
  constr -> constr list option

val solve_pattern_eqn : env -> constr list -> constr -> constr

val noccur_evar : env -> evar_map -> Evar.t -> constr -> bool

exception IllTypedInstance of env * types * types

(* May raise IllTypedInstance if types are not convertible *)
val check_evar_instance :
  evar_map -> existential_key -> constr -> conv_fun -> evar_map

val remove_instance_local_defs :
  evar_map -> existential_key -> constr array -> constr list

val get_type_of_refresh : 
  ?polyprop:bool -> ?lax:bool -> env -> evar_map -> constr -> evar_map * types

val recheck_applications :            (bool ->
            Environ.env ->
            Evd.evar_map ->
            Reduction.conv_pb ->
            Term.types -> Term.types -> unification_result) ->
           Environ.env -> Evd.evar_map ref -> Term.constr -> unit

val invert_definition : unify_flags ->           (bool ->
            Environ.env ->
            Evd.evar_map ->
            Reduction.conv_pb ->
            Term.types -> Term.constr -> unification_result) ->
           bool ->
           bool ->
           Environ.env ->
           Evd.evar_map ->
           bool option ->
           Evd.evar * Constr.constr array ->
           Term.constr -> Evd.evar_map * Term.constr

type evar_projection =
| ProjectVar
| ProjectEvar of existential * evar_info * Names.Id.t * evar_projection
  
val find_projectable_vars :            bool ->
           Term.constr list Names.Id.Map.t * Term.constr list Int.Map.t ->
           Evd.evar_map ->
           Term.constr ->
           (Term.constr * Term.constr option * Names.Id.t) list
           Names.Id.Map.t -> (Names.Id.t * evar_projection) list

  val assoc_up_to_alias :            Evd.evar_map ->
           Term.constr list Names.Id.Map.t * Term.constr list Int.Map.t ->
           Term.constr ->
           Term.constr -> (Term.constr * Term.constr option * Names.Id.t) list -> Names.Id.t

val normalize_alias_opt : Term.constr list Names.Id.Map.t * Term.constr list Int.Map.t ->
           Term.constr -> Term.constr option

