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
open Univ

(*s Cooking the constants. *)

type work_list = (universe_list * Id.t array) Cmap.t * 
  (universe_list * Id.t array) Mindmap.t

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

let instantiate_my_gr gr u =
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)

let cache = (Hashtbl.create 13 : 
	     (my_global_reference, my_global_reference * (universe_list * constr array)) Hashtbl.t)

let clear_cooking_sharing () = Hashtbl.clear cache

let share r (cstl,knl) =
  try Hashtbl.find cache r
  with Not_found ->
  let f,(u,l) =
    match r with
    | IndRef (kn,i) ->
	IndRef (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	ConstructRef ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
	ConstRef (pop_con cst), Cmap.find cst cstl in
  let c = (f, (u, Array.map mkVar l)) in
  Hashtbl.add cache r c;
  (* has raised Not_found if not in work_list *)
  c

let share_univs r u cache =
  let r', (u', args) = share r cache in
    mkApp (instantiate_my_gr r' (List.append u' u), args)

let update_case_info ci modlist =
  try
    let ind, n =
      match share (IndRef ci.ci_ind) modlist with
      | (IndRef f,(u,l)) -> (f, Array.length l)
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

      | Ind (ind,u) ->
	  (try
	    share_univs (IndRef ind) u modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Construct (cstr,u) ->
	  (try
	     share_univs (ConstructRef cstr) u modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Const (cst,u) ->
	  (try
	    share_univs (ConstRef cst) u modlist
	   with
	    | Not_found -> map_constr substrec c)

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
  d_abstract : named_context Univ.in_universe_context;
  d_modlist : work_list }

type inline = bool

type result =
  constant_def * constant_type * bool * Univ.universe_context * inline
    * Sign.section_context option

let on_body f = function
  | Undef inl -> Undef inl
  | Def cs -> Def (Lazyconstr.from_val (f (Lazyconstr.force cs)))
  | OpaqueDef lc ->
    OpaqueDef (Lazyconstr.opaque_from_val (f (Lazyconstr.force_opaque lc)))

let constr_of_def = function
  | Undef _ -> assert false
  | Def cs -> Lazyconstr.force cs
  | OpaqueDef lc -> Lazyconstr.force_opaque lc

let univ_variables_of c = 
  let rec aux univs c = 
    match kind_of_term c with
    | Sort (Type u) ->
      (match Univ.universe_level u with
      | Some l -> Univ.LSet.add l univs
      | None -> univs)
    | Term.Const (_, u) | Term.Ind (_, u) | Term.Construct (_, u) -> 
      Univ.UList.levels u
    | _ -> fold_constr aux univs c
  in aux Univ.LSet.empty c

let cook_constant env r =
  let cb = r.d_from in
  let to_abstract, abs_ctx = r.d_abstract in
  let hyps = Sign.map_named_context (expmod_constr r.d_modlist) to_abstract in
  let body = on_body
    (fun c -> abstract_constant_body (expmod_constr r.d_modlist c) hyps)
    cb.const_body
  in
  let const_hyps =
    Sign.fold_named_context (fun (h,_,_) hyps ->
      List.filter (fun (id,_,_) -> not (Id.equal id h)) hyps)
      hyps ~init:cb.const_hyps in
  let typ = 
    abstract_constant_type (expmod_constr r.d_modlist cb.const_type) hyps 
  in
  let univs = 
    if cb.const_polymorphic then
      union_universe_context abs_ctx cb.const_universes
    else cb.const_universes
  in
  (body, typ, cb.const_polymorphic, univs, cb.const_inline_code, 
   Some const_hyps)
