(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ

(** We introduce here the global environment of the system,
    and we declare it as a synchronized table. *)

module GlobalSafeEnv : sig

  val safe_env : unit -> Safe_typing.safe_environment
  val set_safe_env : Safe_typing.safe_environment -> unit
  val join_safe_environment : unit -> unit

end = struct

let global_env = ref Safe_typing.empty_environment

let join_safe_environment () =
  global_env := Safe_typing.join_safe_environment !global_env

let prune_safe_environment env = Safe_typing.prune_safe_environment env
(* XXX TODO pass args so that these functions can stop at the current
 * file boundaries *)
let () =
  Summary.declare_summary "Global environment"
    { Summary.freeze_function = (function
        | `Yes -> join_safe_environment (); !global_env
        | `No -> !global_env
        | `Shallow -> prune_safe_environment !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := Safe_typing.empty_environment) }

let assert_not_parsing () =
  if !Flags.we_are_parsing then
    Errors.anomaly (
      Pp.strbrk"The global environment cannot be accessed during parsing")

let safe_env () = assert_not_parsing(); !global_env

let set_safe_env e = global_env := e

end

let safe_env = GlobalSafeEnv.safe_env
let join_safe_environment = GlobalSafeEnv.join_safe_environment

let env () = Safe_typing.env_of_safe_env (safe_env ())

let env_is_initial () = Safe_typing.is_initial (safe_env ())

(** Turn ops over the safe_environment state monad to ops on the global env *)

let globalize0 f = GlobalSafeEnv.set_safe_env (f (safe_env ()))

let globalize f =
  let res,env = f (safe_env ()) in GlobalSafeEnv.set_safe_env env; res

let globalize_with_summary fs f =
  let res,env = f (safe_env ()) in
  Summary.unfreeze_summaries fs;
  GlobalSafeEnv.set_safe_env env;
  res

(** [Safe_typing] operations, now operating on the global environment *)

let i2l = Label.of_id

let push_named_assum a = globalize0 (Safe_typing.push_named_assum a)
let push_named_def d = globalize0 (Safe_typing.push_named_def d)
let add_constraints c = globalize0 (Safe_typing.add_constraints c)
let push_context_set c = globalize0 (Safe_typing.push_context_set c)
let push_context c = globalize0 (Safe_typing.push_context c)

let set_engagement c = globalize0 (Safe_typing.set_engagement c)
let add_constant dir id d = globalize (Safe_typing.add_constant dir (i2l id) d)
let add_mind dir id mie = globalize (Safe_typing.add_mind dir (i2l id) mie)
let add_modtype id me inl = globalize (Safe_typing.add_modtype (i2l id) me inl)
let add_module id me inl = globalize (Safe_typing.add_module (i2l id) me inl)
let add_include me ismod inl = globalize (Safe_typing.add_include me ismod inl)

let start_module id = globalize (Safe_typing.start_module (i2l id))
let start_modtype id = globalize (Safe_typing.start_modtype (i2l id))

let end_module fs id mtyo =
  globalize_with_summary fs (Safe_typing.end_module (i2l id) mtyo)

let end_modtype fs id =
  globalize_with_summary fs (Safe_typing.end_modtype (i2l id))

let add_module_parameter mbid mte inl =
  globalize (Safe_typing.add_module_parameter mbid mte inl)

(** Queries on the global environment *)

let universes () = universes (env())
let named_context () = named_context (env())
let named_context_val () = named_context_val (env())

let lookup_named id = lookup_named id (env())
let lookup_constant kn = lookup_constant kn (env())
let lookup_inductive ind = Inductive.lookup_mind_specif (env()) ind
let lookup_pinductive (ind,_) = Inductive.lookup_mind_specif (env()) ind
let lookup_mind kn = lookup_mind kn (env())

let lookup_module mp = lookup_module mp (env())
let lookup_modtype kn = lookup_modtype kn (env())

let exists_objlabel id = Safe_typing.exists_objlabel id (safe_env ())

(** Operations on kernel names *)

let constant_of_delta_kn kn =
  let resolver,resolver_param = Safe_typing.delta_of_senv (safe_env ())
  in
  (* TODO : are resolver and resolver_param orthogonal ?
     the effect of resolver is lost if resolver_param isn't
     trivial at that spot. *)
  Mod_subst.constant_of_deltas_kn resolver_param resolver kn

let mind_of_delta_kn kn =
  let resolver,resolver_param = Safe_typing.delta_of_senv (safe_env ())
  in
  (* TODO idem *)
  Mod_subst.mind_of_deltas_kn resolver_param resolver kn

(** Operations on libraries *)

let start_library dir = globalize (Safe_typing.start_library dir)
let export s = Safe_typing.export (safe_env ()) s
let import cenv digest = globalize (Safe_typing.import cenv digest)


(** Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps =
  reset_with_named_context hyps (env())

open Globnames

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

let type_of_global_unsafe r = 
  let env = env() in
  match r with
  | VarRef id -> Environ.named_type id env
  | ConstRef c -> 
     let cb = Environ.lookup_constant c env in cb.Declarations.const_type
  | IndRef ind ->
     let (mib, oib) = Inductive.lookup_mind_specif env ind in
       oib.Declarations.mind_arity.Declarations.mind_user_arity
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
     let inst = Univ.UContext.instance mib.Declarations.mind_universes in
       Inductive.type_of_constructor (cstr,inst) specif


let is_polymorphic r = 
  let env = env() in
  match r with
  | VarRef id -> false
  | ConstRef c -> 
     let cb = Environ.lookup_constant c env in cb.Declarations.const_polymorphic
  | IndRef ind ->
     let (mib, oib) = Inductive.lookup_mind_specif env ind in
       mib.Declarations.mind_polymorphic
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       mib.Declarations.mind_polymorphic

let current_dirpath () = 
  Safe_typing.current_dirpath (safe_env ())

let with_global f = 
  let (a, ctx) = f (env ()) (current_dirpath ()) in
    push_context_set ctx; a

(* spiwack: register/unregister functions for retroknowledge *)
let register field value by_clause =
  globalize0 (Safe_typing.register field (kind_of_term value) by_clause)

let register_inline c = globalize0 (Safe_typing.register_inline c)
