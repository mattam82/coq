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
open Context
open Declarations
open Environ
open Entries
open Typeops
open Fast_typeops

let debug = true
let prerr_endline =
  if debug then prerr_endline else fun _ -> ()

let constrain_type env j poly = function
  | None ->
    if not poly then (* Old-style polymorphism *)
      make_polymorphic_if_constant_for_ind env j
    else RegularArity j.uj_type
  | Some t ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
	assert (eq_constr t tj.utj_val);
	RegularArity t

let local_constrain_type env j = function
  | None ->
      j.uj_type
  | Some t ->
      let tj = infer_type env t in
      let _ = judge_of_cast env j DEFAULTcast tj in
      assert (eq_constr t tj.utj_val);
      t

(* Insertion of constants and parameters in environment. *)

let handle_side_effects env body side_eff =
  let handle_sideff t se =
    let cbl = match se with
      | SEsubproof (c,cb) -> [c,cb]
      | SEscheme (cl,_) -> List.map (fun (_,c,cb) -> c,cb) cl in
    let cname c = 
      let name = string_of_con c in
      for i = 0 to String.length name - 1 do
        if name.[i] == '.' || name.[i] == '#' then name.[i] <- '_' done;
      Name (id_of_string name) in
    let rec sub c i x = match kind_of_term x with
      | Const (c',_) when eq_constant c c' -> mkRel i
      | _ -> map_constr_with_binders ((+) 1) (sub c) i x in
    let fix_body (c,cb) t =
      match cb.const_body with
      | Undef _ -> assert false
      | Def b ->
          let b = Lazyconstr.force b in
          let b_ty = Typeops.type_of_constant_type env cb.const_type in
          let t = sub c 1 (Vars.lift 1 t) in
          mkLetIn (cname c, b, b_ty, t)
      | OpaqueDef b -> 
          let b = Lazyconstr.force_opaque (Future.force b) in
          let b_ty = Typeops.type_of_constant_type env cb.const_type in
          let t = sub c 1 (Vars.lift 1 t) in
          mkApp (mkLambda (cname c, b_ty, t), [|b|]) in
    List.fold_right fix_body cbl t
  in
  (* CAVEAT: we assure a proper order *)
  Declareops.fold_side_effects handle_sideff body
    (Declareops.uniquize_side_effects side_eff)

(* what is used for debugging only *)
let infer_declaration ?(what="UNKNOWN") env kn dcl =
  match dcl with
  | DefinitionEntry c ->
    let ctx, entry_body = c.const_entry_secctx, c.const_entry_body in
      if c.const_entry_opaque && not (Option.is_empty c.const_entry_type) then
        let id = "infer_declaration " ^ what in
        let body =
          Future.chain ~id entry_body (fun (body, side_eff) ->
            let body = handle_side_effects env body side_eff in
	    let env = push_context (Future.force c.const_entry_universes) env in
            let j = infer env body in
            let j =
              {uj_val = hcons_constr j.uj_val;
               uj_type = hcons_constr j.uj_type} in
	    let _typ = constrain_type env j
	      c.const_entry_polymorphic c.const_entry_type in
            Lazyconstr.opaque_from_val j.uj_val) in
        let def = OpaqueDef body in
        let typ = match c.const_entry_type with
        | None -> assert false
        | Some typ -> RegularArity typ in
          def, typ, None, c.const_entry_polymorphic, 
	  c.const_entry_universes, c.const_entry_inline_code, ctx
      else
        let body, side_eff = Future.force entry_body in
        let body = handle_side_effects env body side_eff in
	let env = push_context (Future.force c.const_entry_universes) env in
	let def, typ, proj = 
	  match c.const_entry_proj with
	  | Some (ind, n, m, ty) ->
            (* FIXME: check projection *)
	    let pb = { proj_ind = ind;
		       proj_npars = n;
		       proj_arg = m;
		       proj_type = ty;
		       proj_body = body }
	    in 
	    let body = mkProj (Option.get kn, mkRel 1) in
	(* TODO: recognize projection *)
	    let context, m = decompose_lam_n_assum (n + 1) body in 
	    let body = it_mkLambda_or_LetIn body context in
	  (* let tj = infer_type env' (Option.get c.const_entry_type) in *)
	      Def (Lazyconstr.from_val (hcons_constr body)),
	      RegularArity (hcons_constr (Option.get c.const_entry_type)), Some pb
	  | None ->
            let j =
              try infer env body 
              with Not_found as e -> 
		prerr_endline ("infer not found " ^ what);
		raise e in
            let j =
              {uj_val = hcons_constr j.uj_val;
               uj_type = hcons_constr j.uj_type} in
            let typ = constrain_type env j c.const_entry_polymorphic c.const_entry_type in
            let def = Def (Lazyconstr.from_val j.uj_val) in
              def, typ, None
	in def, typ, proj, c.const_entry_polymorphic,
	  c.const_entry_universes, c.const_entry_inline_code, ctx
  | ParameterEntry (ctx,poly,(t,uctx),nl) ->
      let env = push_context uctx env in
      let j = infer env t in
      let t = hcons_constr (Typeops.assumption_of_judgment env j) in
      Undef nl, RegularArity t, None, poly, Future.from_val uctx, false, ctx

let global_vars_set_constant_type env = function
  | RegularArity t -> global_vars_set env t
  | TemplateArity (ctx,_) ->
      Context.fold_rel_context
        (fold_rel_declaration
	  (fun t c -> Id.Set.union (global_vars_set env t) c))
      ctx ~init:Id.Set.empty

let build_constant_declaration kn env (def,typ,proj,poly,univs,inline_code,ctx) =
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map pi1 l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      error ("The following section variable are used but not declared:\n"^
        (String.concat ", " (List.map Id.to_string
          (Id.Set.elements (Idset.diff inferred_set declared_set))))) in
  (* We try to postpone the computation of used section variables *)
  let hyps, def = 
    match ctx with
    | None when not (List.is_empty (named_context env)) -> 
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set_constant_type env typ in
        let ids_def = match def with
        | Undef _ -> Idset.empty
        | Def cs -> global_vars_set env (Lazyconstr.force cs)
        | OpaqueDef lc -> 
            (* we force so that cst are added to the env immediately after *)
            ignore(Future.join univs);
            global_vars_set env (Lazyconstr.force_opaque (Future.force lc)) in
        keep_hyps env (Idset.union ids_typ ids_def), def
    | None -> [], def (* Empty section context: no need to check *)
    | Some declared ->
        (* We use the declared set and chain a check of correctness *)
        declared,
        match def with
        | Undef _ as x -> x (* nothing to check *)
        | Def cs as x ->
            let ids_typ = global_vars_set_constant_type env typ in
            let ids_def = global_vars_set env (Lazyconstr.force cs) in
            let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
            check declared inferred;
            x
        | OpaqueDef lc -> (* In this case we can postpone the check *)
            OpaqueDef (Future.chain ~id:(string_of_con kn) lc (fun lc ->
              let ids_typ = global_vars_set_constant_type env typ in
              let ids_def =
                global_vars_set env (Lazyconstr.force_opaque lc) in
              let inferred = keep_hyps env (Idset.union ids_typ ids_def) in
              check declared inferred; lc)) in
  let tps = 
    match proj with
    | None -> Cemitcodes.from_val (compile_constant_body env def)
    | Some pb ->
      Cemitcodes.from_val (compile_constant_body env (Def (Lazyconstr.from_val pb.proj_body)))
  in
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
  build_constant_declaration kn env 
    (infer_declaration ~what:(string_of_con kn) env (Some kn) ce)

let translate_recipe env kn r =
  build_constant_declaration kn env (Cooking.cook_constant env r)

let translate_local_def env id centry =
  let def,typ,proj,poly,univs,inline_code,ctx =
    infer_declaration ~what:(string_of_id id) env None (DefinitionEntry centry) in
  let typ = type_of_constant_type env typ in
    def, typ, univs

let translate_local_assum env t =
  let j = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    t

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let handle_side_effects env ce = { ce with
  const_entry_body = Future.chain ~id:"handle_side_effects" 
    ce.const_entry_body (fun (body, side_eff) ->
    handle_side_effects env body side_eff, Declareops.no_seff);
}
