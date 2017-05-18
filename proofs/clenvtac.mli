(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Legacy components of the previous proof engine. *)

open Term
open Clenv
open Tacexpr
open Unification

(** Tactics *)
val unify : ?flags:unify_flags -> ?with_ho:bool -> constr -> unit Proofview.tactic
val clenv_refine : evars_flag -> ?with_classes:bool -> clausenv -> unit Proofview.tactic
val res_pf : ?with_evars:evars_flag -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic

val clenv_pose_dependent_evars : evars_flag -> clausenv -> clausenv
val clenv_value_cast_meta : clausenv -> constr

val clenv_refine2 :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags -> 
  clause -> unit Proofview.tactic

val clenv_refine_no_check :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags -> 
  clause -> unit Proofview.tactic
                                                                             
val clenv_refine_bindings :
  ?with_evars:evars_flag -> ?with_classes:bool -> ?shelve_subgoals:bool ->
  ?flags:unify_flags ->
  hyps_only:bool -> delay_bindings:bool -> Constr.constr Misctypes.bindings ->
  clause -> unit Proofview.tactic

val clenv_solve_clause_constraints :
  ?flags:unify_flags -> with_ho:bool -> clause -> clause Proofview.tactic

val clenv_check_dep_holes : evars_flag -> Evd.evar_map -> clause -> Goal.goal list Proofview.tactic
       
(** Assumes the clause is typable in the focused tactic's sigma *)
val clenv_unify_concl : Evarconv.unify_flags -> Clenv.clause ->
                        (Evd.evar_map * Clenv.clause) Ftactic.t

val rename_term : Environ.env -> Evd.evar_map -> constr -> Evd.evar_map * constr

(** Debug *)
val debug_print_shelf : string -> unit Proofview.tactic
