(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Entries
open Declarations
open Univ

(** Type checking for some inductive entry.
    Returns:
    - environment with inductives + parameters in rel context
    - abstracted universes
    - checked variance info
    - record entry (checked to be OK)
    - parameters
    - for each inductive,
      (arity * constructors) (with params)
      * (indices * splayed constructor types) (both without params)
      * top allowed elimination
 *)
val typecheck_inductive : env -> mutual_inductive_entry ->
  env
  * universes * Univ.Variance.t array option
  * Names.Id.t array option option
  * Constr.rel_context
  * ((inductive_arity * Constr.types array) *
     (Constr.rel_context * (Constr.rel_context * Constr.types) array) *
     Sorts.family)
    array

type univ_info = { ind_squashed : bool; ind_has_relevant_arg : bool;
                   ind_min_univ : Universe.t option; (* Some for template *)
                   ind_univ : Universe.t }

val check_univ_leq :  ?is_real_arg:bool ->
           Environ.env -> Univ.Universe.t -> univ_info -> univ_info
