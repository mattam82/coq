(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open Errors
open Util
open Names
open Term
open Sign
open Declarations
open Environ

(*s Cooking the constants. *)

type work_list = Id.t array Cmap.t * Id.t array Mindmap.t

let pop_dirpath p = match DirPath.repr p with
  | [] -> anomaly ~label:"dirpath_prefix" (Pp.str "empty dirpath")
  | _::l -> DirPath.make l

let pop_mind kn =
  let (mp,dir,l) = Names.repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (pop_dirpath dir) l

type my_global_reference =
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

let cache = (Hashtbl.create 13 : (my_global_reference, constr) Hashtbl.t)

let clear_cooking_sharing () = Hashtbl.clear cache

let share r (cstl,knl) =
  try Hashtbl.find cache r
  with Not_found ->
  let f,l =
    match r with
    | IndRef (kn,i) ->
	mkInd (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	mkConstruct ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
	mkConst (pop_con cst), Cmap.find cst cstl in
  let c = mkApp (f, Array.map mkVar l) in
  Hashtbl.add cache r c;
  (* has raised Not_found if not in work_list *)
  c

let update_case_info ci modlist =
  try
    let ind, n =
      match kind_of_term (share (IndRef ci.ci_ind) modlist) with
      | App (f,l) -> (destInd f, Array.length l)
      | Ind ind -> ind, 0
      | _ -> assert false in
    { ci with ci_ind = ind; ci_npar = ci.ci_npar + n }
  with Not_found ->
    ci

let empty_modlist = (Cmap.empty, Mindmap.empty)

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr modlist c =
  let rec substrec c =
    match kind_of_term c with
      | Case (ci,p,t,br) ->
	  map_constr substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind ind ->
	  (try
	    share (IndRef ind) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Construct cstr ->
	  (try
	    share (ConstructRef cstr) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Const cst ->
	  (try
	    share (ConstRef cst) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Proj (p, c') ->
          (try 
	     match kind_of_term (share (ConstRef p) modlist) with
	     | Const p' -> mkProj (p', map_constr substrec c')
	     | _ -> mkProj (p, map_constr substrec c')
	   with Not_found -> map_constr substrec c)

  | _ -> map_constr substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

let abstract_constant_type =
   List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c)

let abstract_constant_body =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

type recipe = {
  d_from : constant_body;
  d_abstract : named_context;
  d_modlist : work_list }

type inline = bool

type result =
  constant_def * constant_type * projection_body option * 
  Univ.constraints * bool * Sign.section_context

let on_body f = function
  | Undef inl -> Undef inl
  | Def cs -> Def (Lazyconstr.from_val (f (Lazyconstr.force cs)))
  | OpaqueDef lc ->
    OpaqueDef (Lazyconstr.opaque_from_val (f (Lazyconstr.force_opaque lc)))

let constr_of_def = function
  | Undef _ -> assert false
  | Def cs -> Lazyconstr.force cs
  | OpaqueDef lc -> Lazyconstr.force_opaque lc

(* Apply the cooking substitution to a projections type. *)
let rename_constant_type n c hyps =
  CList.fold_left_i
    (fun i c (id, body, t) -> 
      match body with
      | Some b -> replace_vars [(id, b)] c
      | None -> replace_vars [(id, mkRel i)] c)
    (n + 1) c hyps

let cook_constant env r =
  let cb = r.d_from in
  let hyps = Sign.map_named_context (expmod_constr r.d_modlist) r.d_abstract in
  let body = on_body
    (fun c -> abstract_constant_body (expmod_constr r.d_modlist c) hyps)
    cb.const_body
  in
  let const_hyps =
    Sign.fold_named_context (fun (h,_,_) hyps ->
      List.filter (fun (id,_,_) -> not (Id.equal id h)) hyps)
      hyps ~init:cb.const_hyps in
  let ty, typ = match cb.const_type with
    | NonPolymorphicType t ->
	let typ = abstract_constant_type (expmod_constr r.d_modlist t) hyps in
	typ, NonPolymorphicType typ
    | PolymorphicArity (ctx,s) ->
	let t = mkArity (ctx,Type s.poly_level) in
	let typ = abstract_constant_type (expmod_constr r.d_modlist t) hyps in
	let j = make_judge (constr_of_def body) typ in
	typ, Typeops.make_polymorphic_if_constant_for_ind env j
  in
  let projection pb =
    let (mind, _), n' =
      try match kind_of_term (share (IndRef (pb.proj_ind,0)) r.d_modlist) with
      | App (f,l) -> (destInd f, Array.length l)
      | Ind ind -> ind, 0
      | _ -> assert false 
      with Not_found -> ((pb.proj_ind,0), 0)
    in 
    let ctx, ty' = decompose_prod_n (n' + pb.proj_npars + 1) ty in
      { proj_ind = mind; proj_npars = pb.proj_npars + n'; proj_arg = pb.proj_arg;
	 proj_type = ty' }
  in
    (body, typ, Option.map projection cb.const_proj, cb.const_constraints, 
		    cb.const_inline_code, Some const_hyps)
