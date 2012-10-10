(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Declarations
open Entries
open Indtypes
open Mod_subst
open Safe_typing

(** This module defines the global environment of Coq.  The functions
   below are exactly the same as the ones in [Safe_typing], operating on
   that global environment. [add_*] functions perform name verification,
   i.e. check that the name given as argument match those provided by
   [Safe_typing]. *)



val safe_env : unit -> safe_environment
val env : unit -> Environ.env

val env_is_empty : unit -> bool

val universes : unit -> universes
val named_context_val : unit -> Environ.named_context_val
val named_context : unit -> Sign.named_context

val env_is_empty : unit -> bool

(** {6 Extending env with variables and local definitions } *)
val push_named_assum : (Id.t * types) -> Univ.constraints
val push_named_def   : (Id.t * constr * types option) -> Univ.constraints

(** {6 ... } *)
(** Adding constants, inductives, modules and module types.  All these
  functions verify that given names match those generated by kernel *)

val add_constant :
  DirPath.t -> Id.t -> global_declaration -> constant
val add_mind        :
  DirPath.t -> Id.t -> mutual_inductive_entry -> mutual_inductive

val add_module      :
 Id.t -> module_entry -> inline -> module_path * delta_resolver
val add_modtype     :
 Id.t -> module_struct_entry -> inline -> module_path
val add_include :
 module_struct_entry -> bool -> inline -> delta_resolver

val add_constraints : constraints -> unit

val set_engagement : engagement -> unit

(** {6 Interactive modules and module types }
   Both [start_*] functions take the [DirPath.t] argument to create a
   [mod_self_id]. This should be the name of the compilation unit. *)

(** [start_*] functions return the [module_path] valid for components
   of the started module / module type *)

val start_module : Id.t -> module_path

val end_module : Summary.frozen ->Id.t ->
  (module_struct_entry * inline) option -> module_path * delta_resolver

val add_module_parameter :
 MBId.t -> module_struct_entry -> inline -> delta_resolver

val start_modtype : Id.t -> module_path
val end_modtype : Summary.frozen -> Id.t -> module_path
val pack_module : unit -> module_body


(** Queries *)
val lookup_named      : variable -> named_declaration
val lookup_constant   : constant -> constant_body
val lookup_inductive  : inductive -> mutual_inductive_body * one_inductive_body
val lookup_pinductive : pinductive -> mutual_inductive_body * one_inductive_body
val lookup_mind       : mutual_inductive -> mutual_inductive_body
val lookup_module     : module_path -> module_body
val lookup_modtype    : module_path -> module_type_body
val constant_of_delta_kn : kernel_name -> constant
val mind_of_delta_kn : kernel_name -> mutual_inductive
val exists_objlabel  : Label.t -> bool

(** Compiled modules *)
val start_library : DirPath.t -> module_path
val export : DirPath.t -> module_path * compiled_library * native_library
val import : compiled_library -> Digest.t ->
  module_path * Nativecode.symbol array

(** {6 ... } *)
(** Function to get an environment from the constants part of the global
 * environment and a given context. *)

val is_polymorphic : Globnames.global_reference -> bool

(* val type_of_global : Globnames.global_reference -> types Univ.in_universe_context_set *)
val type_of_global_unsafe : Globnames.global_reference -> types 
val env_of_context : Environ.named_context_val -> Environ.env

(** spiwack: register/unregister function for retroknowledge *)
val register : Retroknowledge.field -> constr -> constr -> unit

(* Modifies the global state, registering new universes *)

val current_dirpath : unit -> Names.dir_path

val with_global : (Environ.env -> Names.dir_path -> 'a in_universe_context_set) -> 'a
