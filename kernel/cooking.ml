(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Declarations
open Environ
open Univ

(*s Cooking the constants. *)

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
  | ProjRef of projection
		 
module RefHash =
struct
  type t = my_global_reference
  let equal gr1 gr2 = match gr1, gr2 with
  | ConstRef c1, ConstRef c2 -> Constant.CanOrd.equal c1 c2
  | IndRef i1, IndRef i2 -> eq_ind i1 i2
  | ConstructRef c1, ConstructRef c2 -> eq_constructor c1 c2
  | ProjRef p1, ProjRef p2 -> Projection.equal p1 p2
  | _ -> false
  open Hashset.Combine
  let hash = function
  | ConstRef c -> combinesmall 1 (Constant.hash c)
  | IndRef i -> combinesmall 2 (ind_hash i)
  | ConstructRef c -> combinesmall 3 (constructor_hash c)
  | ProjRef p -> combinesmall 4 (Projection.hash p)
end

module RefTable = Hashtbl.Make(RefHash)

let instantiate_my_gr gr u arg l =
  match gr with
  | ConstRef c -> mkApp (mkConstU (c, u), l)
  | IndRef i -> mkApp (mkIndU (i, u), l)
  | ConstructRef c -> mkApp (mkConstructU (c, u), l)
  | ProjRef p -> mkProj (p, Option.get arg)

let share cache r (cstl,knl) =
  try RefTable.find cache r
  with Not_found ->
  let f,(u,l) =
    match r with
    | IndRef (kn,i) ->
	IndRef (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	ConstructRef ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
       ConstRef (pop_con cst), Cmap.find cst cstl
    | ProjRef p ->
       let kn = Projection.record p in
       let _r = Mindmap.find kn knl in
       let mind = pop_mind kn in
       let p' = Projection.make mind (Projection.index p)
				(Projection.unfolded p) in
       ProjRef p', (Univ.Instance.empty, [||])
  in
  let c = (f, (u, Array.map mkVar l)) in
  RefTable.add cache r c;
  c

let share_univs cache r u l arg =
  let r', (u', args) = share cache r l in
    instantiate_my_gr r' (Instance.append u' u) arg args

let update_case_info cache ci modlist =
  try
    let ind, n =
      match share cache (IndRef ci.ci_ind) modlist with
      | (IndRef f,(u,l)) -> (f, Array.length l)
      | _ -> assert false in
    { ci with ci_ind = ind; ci_npar = ci.ci_npar + n }
  with Not_found ->
    ci

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr cache modlist c =
  let share_univs = share_univs cache in
  let update_case_info = update_case_info cache in
  let rec substrec c =
    match kind_of_term c with
      | Case (ci,p,t,br) ->
	  map_constr substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind (ind,u) ->
	  (try
	    share_univs (IndRef ind) u modlist None
	   with
	    | Not_found -> map_constr substrec c)

      | Construct (cstr,u) ->
	  (try
	     share_univs (ConstructRef cstr) u modlist None
	   with
	    | Not_found -> map_constr substrec c)

      | Const (cst,u) ->
	  (try
	    share_univs (ConstRef cst) u modlist None
	   with
	    | Not_found -> map_constr substrec c)

      | Proj (p, c') ->
         (try
	     share_univs (ProjRef p) Univ.Instance.empty modlist (Some c')
	   with Not_found -> map_constr substrec c)

  | _ -> map_constr substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

let abstract_constant_type =
   List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c)

let abstract_constant_body =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

type recipe = { from : constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type result =
  constant_def * constant_type * 
    bool * constant_universes * inline
    * Context.section_context option

let on_body ml cache hy f = function
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (f (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_direct_opaque ~cook_constr:f
						   { Opaqueproof.modlist = ml; abstract = hy } o)
  | Projection p as x ->
     let r', (u', args) = share cache (ProjRef p) ml in
       match r' with
       | ProjRef p -> Projection p
       | _ -> assert false

let constr_of_def otab = function
  | Undef _ -> assert false
  | Def cs -> Mod_subst.force_constr cs
  | OpaqueDef lc -> Opaqueproof.force_proof otab lc
  | Projection _ -> assert false
			  
let expmod_constr_subst cache modlist subst c =
  let c = expmod_constr cache modlist c in
    Vars.subst_univs_level_constr subst c

let cook_constr { Opaqueproof.modlist ; abstract } c =
  let cache = RefTable.create 13 in
  let expmod = expmod_constr_subst cache modlist (pi2 abstract) in
  let hyps = Context.map_named_context expmod (pi1 abstract) in
  abstract_constant_body (expmod c) hyps

let lift_univs cb subst =
  if cb.const_polymorphic && not (Univ.LMap.is_empty subst) then
    let inst = Univ.UContext.instance cb.const_universes in
    let cstrs = Univ.UContext.constraints cb.const_universes in
    let len = Univ.LMap.cardinal subst in
    let subst = 
      Array.fold_left_i (fun i acc v -> Univ.LMap.add (Level.var i) (Level.var (i + len)) acc)
	subst (Univ.Instance.to_array inst)
    in
    let cstrs' = Univ.subst_univs_level_constraints subst cstrs in
      subst, Univ.UContext.make (inst,cstrs')
  else subst, cb.const_universes

let cook_constant env { from = cb; info } =
  let { Opaqueproof.modlist; abstract } = info in
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, univs = lift_univs cb usubst in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps = Context.map_named_context expmod abstract in
  let body = on_body modlist cache (hyps, usubst, abs_ctx)
    (fun c -> abstract_constant_body (expmod c) hyps)
    cb.const_body
  in
  let const_hyps =
    Context.fold_named_context (fun (h,_,_) hyps ->
      List.filter (fun (id,_,_) -> not (Id.equal id h)) hyps)
      hyps ~init:cb.const_hyps in
  let typ = match cb.const_type with
    | RegularArity t ->
  	let typ =
          abstract_constant_type (expmod t) hyps in
  	RegularArity typ
    | TemplateArity (ctx,s) ->
  	let t = mkArity (ctx,Type s.template_level) in
  	let typ = abstract_constant_type (expmod t) hyps in
  	let j = make_judge (constr_of_def (opaque_tables env) body) typ in
  	Typeops.make_polymorphic_if_constant_for_ind env j
  in
  let univs = 
    let abs' = 
      if cb.const_polymorphic then abs_ctx
      else instantiate_univ_context abs_ctx
    in
      UContext.union abs' univs
  in
    (body, typ, cb.const_polymorphic, univs, cb.const_inline_code, 
     Some const_hyps)

(* let cook_constant_key = Profile.declare_profile "cook_constant" *)
(* let cook_constant = Profile.profile2 cook_constant_key cook_constant *)

let expmod_constr modlist c = expmod_constr (RefTable.create 13) modlist c
