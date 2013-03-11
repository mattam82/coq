(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open Errors
open Util
open Names
open Univ
open Term
open Declarations
open Environ
open Entries
open Typeops

let constrain_type env j ctx poly = function
  | None -> j.uj_type, ctx
  | Some t ->
      let tj, ctx' = infer_type env t in
      let ctx = union_universe_context_set ctx ctx' in
      let j, cst = judge_of_cast env j DEFAULTcast tj in
	(* TODO*)
	check_consistent_constraints ctx cst;
	assert (eq_constr t tj.utj_val);
	t, add_constraints_ctx ctx cst

let local_constrain_type env j = function
  | None ->
      j.uj_type
  | Some t ->
      let (tj,ctx) = infer_type env t in
      let (_,cst) = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      check_consistent_constraints ctx cst;
      t

let translate_local_def env (b,topt) =
  let (j,ctx) = infer env b in
  let typ = local_constrain_type env j topt in
    (j.uj_val,typ,ctx)

let translate_local_assum env t =
  let (j,cst) = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    (t,cst)

(* Insertion of constants and parameters in environment. *)

let infer_declaration env = function
  | DefinitionEntry c ->
    let env' = push_constraints_to_env c.const_entry_universes env in
    let (j,cst) = infer env' c.const_entry_body in
    let j =
      {uj_val = hcons_constr j.uj_val;
       uj_type = hcons_constr j.uj_type} in
    let (typ,cst) = constrain_type env' j cst
      c.const_entry_polymorphic c.const_entry_type in
    let def =
      if c.const_entry_opaque
      then OpaqueDef (Lazyconstr.opaque_from_val j.uj_val)
      else Def (Lazyconstr.from_val j.uj_val)
    in
    let univs = check_context_subset cst c.const_entry_universes in
    let proj = 
      match c.const_entry_proj with
      | Some (ind, n, m, ty) ->
        (* FIXME: check projection *)
        let pb = { proj_ind = ind;
		   proj_npars = n;
		   proj_arg = m;
		   proj_type = ty }
	in Some pb
      | None -> None
    in
      def, typ, proj, c.const_entry_polymorphic, univs,
        c.const_entry_inline_code, c.const_entry_secctx
  | ParameterEntry (ctx,(t,uctx),nl) ->
    let env' = push_constraints_to_env uctx env in
    let (j,cst) = infer env' t in
    let t = hcons_constr (Typeops.assumption_of_judgment env j) in
    (* let univs = check_context_subset cst uctx in *) (*FIXME*)
    let univs = Univ.context_of_universe_context_set uctx in
      Undef nl, t, None, false, univs, false, ctx
      
let global_vars_set_constant_type env = global_vars_set env

let build_constant_declaration env kn (def,typ,proj,poly,univs,inline_code,ctx) =
  let hyps = 
    let inferred =
      let ids_typ = global_vars_set_constant_type env typ in
      let ids_def = match def with
      | Undef _ -> Id.Set.empty
      | Def cs -> global_vars_set env (Lazyconstr.force cs)
      | OpaqueDef lc -> 
          global_vars_set env (Lazyconstr.force_opaque lc) in
      keep_hyps env (Id.Set.union ids_typ ids_def) in
    let declared = match ctx with
      | None -> inferred 
      | Some declared -> declared in
    let mk_set l = List.fold_right Id.Set.add (List.map pi1 l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      error ("The following section variable are used but not declared:\n"^
        (String.concat ", " (List.map Id.to_string
          (Id.Set.elements (Id.Set.diff inferred_set declared_set)))));
    declared in
  let tps = Cemitcodes.from_val (compile_constant_body env def) in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_proj = proj;
    const_body_code = tps;
    const_polymorphic = poly;
    const_universes = univs;
    const_native_name = ref NotLinked;
    const_inline_code = inline_code }

(*s Global and local constant declaration. *)

let translate_constant env kn ce =
  build_constant_declaration env kn (infer_declaration env ce)

let translate_recipe env kn r =
  build_constant_declaration env kn 
    (let def,typ,proj,poly,cst,inline,hyps = Cooking.cook_constant env r in
     def,typ,proj,poly,cst,inline,hyps)

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie
