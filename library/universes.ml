(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Sign
open Environ
open Locus
open Univ

(** Fresh levels *)

let new_univ_level =
  let n = ref 0 in 
    fun dp -> incr n; 
      Univ.Level.make dp !n

let fresh_level () = new_univ_level (Global.current_dirpath ())

(* TODO: remove *)
let new_univ dp = Univ.Universe.make (new_univ_level dp)
let new_Type dp = mkType (new_univ dp)
let new_Type_sort dp = Type (new_univ dp)

let fresh_universe_instance (ctx, _) =
  List.map (fun _ -> new_univ (Global.current_dirpath ())) ctx

let fresh_instance_from_context (vars, cst as ctx) =
  let inst = fresh_universe_instance ctx in
  let subst = make_universe_subst inst ctx in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), constraints

let fresh_instance (ctx, _) =
  List.fold_left (fun s _ -> LSet.add (fresh_level ()) s) LSet.empty ctx

let fresh_instance_from (vars, cst as ctx) =
  let ctx' = fresh_instance ctx in
  let inst = Univ.UList.of_llist (LSet.elements ctx') in
  let subst = make_universe_subst inst ctx in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), (ctx', constraints)

(** Fresh universe polymorphic construction *)

let fresh_constant_instance env c =
  let cb = lookup_constant c env in
    if cb.Declarations.const_polymorphic then
      let (inst,_), ctx = fresh_instance_from cb.Declarations.const_universes in
	((c, inst), ctx)
    else ((c,[]), Univ.empty_universe_context_set)

let fresh_inductive_instance env ind = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
	((ind,inst), ctx)
    else ((ind,[]), Univ.empty_universe_context_set)

let fresh_constructor_instance env (ind,i) = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_polymorphic then
      let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
	(((ind,i),inst), ctx)
    else (((ind,i),[]), Univ.empty_universe_context_set)

open Globnames
let fresh_global_instance env gr =
  match gr with
  | VarRef id -> mkVar id, Univ.empty_universe_context_set
  | ConstRef sp -> 
     let c, ctx = fresh_constant_instance env sp in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = fresh_constructor_instance env sp in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = fresh_inductive_instance env sp in
       mkIndU c, ctx

let constr_of_global gr =
  let c, ctx = fresh_global_instance (Global.env ()) gr in
    Global.add_constraints (snd ctx); c

let fresh_global_or_constr_instance env = function
  | IsConstr c -> c, Univ.empty_universe_context_set
  | IsGlobal gr -> fresh_global_instance env gr

let global_of_constr c =
  match kind_of_term c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, []
  | _ -> raise Not_found

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, Univ.empty_universe_context_set
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
       if cb.const_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from cb.const_universes in
	   subst_univs_constr subst cb.const_type, ctx
       else cb.const_type, Univ.empty_universe_context_set

  | IndRef ind ->
     let (mib, oib) = Inductive.lookup_mind_specif env ind in
       if mib.mind_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
	   subst_univs_constr subst oib.mind_arity.mind_user_arity, ctx
       else oib.mind_arity.mind_user_arity, Univ.empty_universe_context_set
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       if mib.mind_polymorphic then
	 let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
	   Inductive.type_of_constructor (cstr,inst) specif, ctx
       else Inductive.type_of_constructor (cstr,[]) specif, Univ.empty_universe_context_set

let type_of_global t = type_of_reference (Global.env ()) t

let fresh_sort_in_family env = function
  | InProp -> prop_sort, Univ.empty_universe_context_set
  | InSet -> set_sort, Univ.empty_universe_context_set
  | InType -> 
    let u = fresh_level () in
      Type (Univ.Universe.make u), Univ.singleton_universe_context_set u

let new_sort_in_family sf =
  fst (fresh_sort_in_family (Global.env ()) sf)

let extend_context (a, ctx) (ctx') =
  (a, Univ.union_universe_context_set ctx ctx')

let new_global_univ () =
  let u = fresh_level () in
    (Univ.Universe.make u, Univ.singleton_universe_context_set u)

(** Simplification *)

module LevelUnionFind = Unionfind.Make (Univ.LSet) (Univ.LMap)

let remove_trivial_constraints cst =
  Constraint.fold (fun (l,d,r as cstr) nontriv ->
    if d <> Lt && eq_levels l r then nontriv
    else if d = Le && is_type0m_univ (Univ.Universe.make l) then nontriv
    else Constraint.add cstr nontriv)
    cst empty_constraint

let add_list_map u t map = 
  let l, d, r = LMap.split u map in
  let d' = match d with None -> [t] | Some l -> t :: l in
  let lr = 
    LMap.merge (fun k lm rm -> 
      match lm with Some t -> lm | None ->
      match rm with Some t -> rm | None -> None) l r
  in LMap.add u d' lr

let find_list_map u map =
  try LMap.find u map with Not_found -> []

module UF = LevelUnionFind
type universe_full_subst = (universe_level * universe) list

exception Stays

let instantiate_univ_variables ucstrsl ucstrsr u (subst, cstrs) =
 (** The universe variable was not fixed yet.
     Compute its level using its lower bound and generate
     the upper bound constraints *)
  let lbound = 
    try
      let r = LMap.find u ucstrsr in
      let lbound = List.fold_left (fun lbound (d, l) -> 
      if d = Le (* l <= ?u *) then (Universe.sup (Universe.make l) lbound)
      else (* l < ?u *) (assert (d = Lt); (Universe.sup (Universe.super (Universe.make l)) lbound)))
	Universe.type0m r
      in Some lbound
    with Not_found ->
      (** No lower bound, choose the minimal level according to the
	  upper bounds (greatest lower bound), if any. *)
      None
  in
  let uinst, cstrs =
    try 
      let l = LMap.find u ucstrsl in
      let lbound, stay =
	match lbound with
	| None -> Universe.make u, true (** No lower bounds but some upper bounds, u has to stay *)
	| Some lbound -> 
	  let stay = Universe.level lbound = None
	  (* u will have to stay if we have to compute its super form. *)
	  in lbound, stay
      in
	try
	  let cstrs =
	    List.fold_left (fun cstrs (d,r) ->
	      if d = Le (* ?u <= r *) then enforce_leq lbound (Universe.make r) cstrs
	      else (* ?u < r *) 
		if not stay then
		  enforce_leq (Universe.super lbound) (Universe.make r) cstrs
		else raise Stays)
	    cstrs l
	  in Some lbound, cstrs
	with Stays ->
	  (** We can't instantiate ?u at all. *)
	  let uu = Universe.make u in
	  let cstrs = enforce_leq lbound uu cstrs in
	  let cstrs = List.fold_left (fun cstrs (d,r) ->
	    let lev = if d == Le then uu else Universe.super uu in
	      enforce_leq lev (Universe.make r) cstrs)
	    cstrs l
	  in None, cstrs
    with Not_found -> lbound, cstrs
  in 
  let subst' = 
    match uinst with
    | None -> subst 
    | Some uinst -> 
      if not (Universe.eq uinst (Universe.make u)) then
	(u, uinst) :: subst
      else subst
  in (subst', cstrs)
  
(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible s =
  let global = LSet.diff s ctx in
  let flexible, rigid = LSet.partition (fun x -> LSet.mem x flexible) (LSet.inter s ctx) in
    (** If there is a global universe in the set, choose it *)
    if not (LSet.is_empty global) then
      let canon = LSet.choose global in
	canon, (LSet.remove canon global, rigid, flexible)
    else (** No global in the equivalence class, choose a rigid one *)
	if not (LSet.is_empty rigid) then
	  let canon = LSet.choose rigid in
	    canon, (global, LSet.remove canon rigid, flexible)
	else (** There are only flexible universes in the equivalence
		 class, choose an arbitrary one. *)
	  let canon = LSet.choose s in
	    canon, (global, rigid, LSet.remove canon flexible)

open Universe

let smartmap_pair f g x =
  let (a, b) = x in
  let a' = f a and b' = g b in
    if a' == a && b' == b then x
    else (a', b')

let has_constraint csts x d y =
  Constraint.exists (fun (l,d',r) ->
    eq_levels x l && d = d' && eq_levels y r)
    csts

let id x = x

(* TODO: handle u+n levels *)
let simplify_max_expressions csts subst = 
  let remove_higher l =
    match Universe.to_levels l with
    | None -> l
    | Some levs ->
      let rec aux found acc = function
	| [] -> if found then Universe.of_levels acc else l
	| ge :: ges -> 
	if List.exists (fun ge' -> has_constraint csts ge Le ge') acc 
	  || List.exists (fun ge' -> has_constraint csts ge Le ge') ges then
	  aux true acc ges
	else aux found (ge :: acc) ges
      in aux false [] levs
  in
    CList.smartmap (smartmap_pair id remove_higher) subst

let subst_puniverses subst (c, u as cu) =
  let u' = CList.smartmap (Univ.subst_univs_level_universe subst) u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_local f subst =
  let rec aux c =
    match kind_of_term c with
    | Evar (evdk, _ as ev) ->
      (match f ev with
      | None -> c
      | Some c -> aux c)
    | Const pu -> 
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_puniverses subst pu in
	if pu' == pu then c else mkConstructU pu'
    | Sort (Type u) ->
      let u' = Univ.subst_univs_level_universe subst u in
	if u' == u then c else mkSort (sort_of_univ u')
    | _ -> map_constr aux c
  in aux

let subst_univs_fn_puniverses subst (c, u as cu) =
  let u' = CList.smartmap (Univ.subst_univs_universe subst) u in
    if u' == u then cu else (c, u')

let subst_univs_puniverses subst cu =
  subst_univs_fn_puniverses (Univ.make_subst subst) cu

let nf_evars_and_universes_gen f subst =
  let rec aux c =
    match kind_of_term c with
    | Evar (evdk, _ as ev) ->
      (match try f ev with Not_found -> None with
      | None -> c
      | Some c -> aux c)
    | Const pu -> 
      let pu' = subst_univs_fn_puniverses subst pu in
	if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_univs_fn_puniverses subst pu in
	if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_univs_fn_puniverses subst pu in
	if pu' == pu then c else mkConstructU pu'
    | Sort (Type u) ->
      let u' = Univ.subst_univs_universe subst u in
	if u' == u then c else mkSort (sort_of_univ u')
    | _ -> map_constr aux c
  in aux

let nf_evars_and_universes_subst f subst =
  nf_evars_and_universes_gen f (Univ.make_subst subst)

let nf_evars_and_universes_opt_subst f subst =
  let subst = fun l -> match LMap.find l subst with None -> raise Not_found | Some l' -> l' in
    nf_evars_and_universes_gen f subst

let subst_univs_full_constr subst c = 
  nf_evars_and_universes_subst (fun _ -> None) subst c

let fresh_universe_context_set_instance (univs, cst) =
  let univs',subst = LSet.fold
    (fun u (univs',subst) ->
      let u' = fresh_level () in
	(LSet.add u' univs', LMap.add u u' subst))
    univs (LSet.empty, LMap.empty)
  in
  let cst' = subst_univs_level_constraints subst cst in
    subst, (univs', cst')

let normalize_univ_variable ~find ~update =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.eq b' b then b
      else update cur b'
  in fun b -> try aux b with Not_found -> Universe.make b

let normalize_univ_variable_opt_subst ectx =
  let find l = 
    match Univ.LMap.find l !ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.eq l l') | None -> true);
    ectx := Univ.LMap.add l (Some b) !ectx; b
  in normalize_univ_variable ~find ~update

let normalize_univ_variable_subst subst =
  let find l = Univ.LMap.find l !subst in
  let update l b =
    assert (match Universe.level b with Some l' -> not (Level.eq l l') | None -> true);
    subst := Univ.LMap.add l b !subst; b in
    normalize_univ_variable ~find ~update

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_universe_subst subst =
  let normlevel = normalize_univ_variable_subst subst in
    subst_univs_universe normlevel

type universe_opt_subst = universe option universe_map
	  
let normalize_univ_variables ctx = 
  let ectx = ref ctx in
  let normalize = normalize_univ_variable_opt_subst ectx in
  let _ = Univ.LMap.iter (fun u _ -> ignore(normalize u)) ctx in
  let undef, def, subst = 
    Univ.LMap.fold (fun u v (undef, def, subst) -> 
      match v with
      | None -> (Univ.LSet.add u undef, def, subst)
      | Some b -> (undef, Univ.LSet.add u def, Univ.LMap.add u b subst))
    !ectx (Univ.LSet.empty, Univ.LSet.empty, Univ.LMap.empty)
  in !ectx, undef, def, subst

let pr_universe_body = function
  | None -> mt ()
  | Some v -> str" := " ++ Univ.Universe.pr v

let pr_universe_opt_subst = Univ.LMap.pr pr_universe_body


let subst_univs_subst u l s = 
  LMap.add u l s
    
let normalize_context_set (ctx, csts) substdef us algs = 
  let uf = UF.create () in
  let noneqs = 
    Constraint.fold (fun (l,d,r) noneqs ->
      if d = Eq then (UF.union l r uf; noneqs) else Constraint.add (l,d,r) noneqs)
    csts Constraint.empty
  in
  let partition = UF.partition uf in
  let subst, eqs = List.fold_left (fun (subst, cstrs) s -> 
    let canon, (global, rigid, flexible) = choose_canonical ctx us s in
    (* Add equalities for globals which can't be merged anymore. *)
    let cstrs = LSet.fold (fun g cst -> 
      Constraint.add (canon, Univ.Eq, g) cst) global cstrs 
    in
    (** Should this really happen? *)
    let subst' = LSet.fold (fun f -> LMap.add f canon)
      (LSet.union rigid flexible) LMap.empty
    in 
    let subst = LMap.union subst' subst in
      (subst, cstrs))
    (LMap.empty, Constraint.empty) partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints, 
     and contains only inequality constraints. *)
  let noneqs = subst_univs_level_constraints subst noneqs in
  (* Compute the left and right set of flexible variables, constraints
     mentionning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr = 
    Constraint.fold (fun (l,d,r as cstr) (noneq, ucstrsl, ucstrsr) -> 
      let lus = LSet.mem l us 
      and rus = LSet.mem r us
      in
      let ucstrsl' = 
	if lus then add_list_map l (d, r) ucstrsl
	else ucstrsl
      and ucstrsr' = 
	if rus then add_list_map r (d, l) ucstrsr
	else ucstrsr
      in 
      let noneqs = 
	if lus || rus then noneq 
	else Constraint.add cstr noneq
      in (noneqs, ucstrsl', ucstrsr'))
    noneqs (empty_constraint, LMap.empty, LMap.empty)
  in
  (* Now we construct the instanciation of each variable. *)
  let ussubst, noneqs = LSet.fold (fun u acc -> 
    let u' = subst_univs_level_level subst u in
      (* Only instantiate the canonical variables *)
      if eq_levels u' u then
	instantiate_univ_variables ucstrsl ucstrsr u' acc
      else acc)
    us ([], noneqs)
  in  
  let uf = UF.create () in
  let subst, ussubst, noneqs =
    let rec aux subst ussubst =
      List.fold_left (fun (subst,usubst') (u, us) ->
        match universe_level us with
  	| Some l -> UF.union u l uf; 
	  let l' = UF.find l uf in
	    if not (Level.eq l' u) then 
	      (Univ.LMap.add u l' subst, usubst')
	    else (subst, usubst')
  	| None -> (** Couldn't find a level, keep the universe? *)
  	    (subst, (u, us) :: usubst'))
      (subst, []) ussubst
    in
    (** Normalize the substitution w.r.t. itself so we get only
  	fully-substituted, normalized universes as the range of the substitution.
  	We need to do it for the initial substitution which is canonical
  	already only at the end. *)
    let rec fixpoint noneqs subst ussubst =
      let subst', ussubst' = aux subst ussubst in
      let ussubst', noneqs =
  	if ussubst == ussubst' then ussubst, noneqs
  	else
  	  let noneqs' = subst_univs_level_constraints subst' noneqs in
  	    simplify_max_expressions noneqs' ussubst',
  	    noneqs'
      in
  	if ussubst' = [] then subst', ussubst', noneqs
  	else
  	  let ussubst' = List.rev ussubst' in
  	    if ussubst' = ussubst then subst', ussubst', noneqs
  	    else fixpoint noneqs subst' ussubst'
    in fixpoint noneqs subst ussubst
  in
  let partition = UF.partition uf in
  let subst, noneqs =
    List.fold_left (fun (subst, cstrs) s ->
      let canon, (global, rigid, flexible) = choose_canonical ctx us s in
      (* Add equalities for globals which can't be merged anymore. *)
      let cstrs = LSet.fold (fun g cst ->
        Constraint.add (canon, Univ.Eq, g) cst) global cstrs
      in
      (* Same for rigids, they can't be subsituted *)
      let cstrs = LSet.fold (fun g cst ->
        Constraint.add (canon, Univ.Eq, g) cst) rigid cstrs
      in
      let subst = LSet.fold (fun f -> LMap.add f canon)
  	flexible subst
      in (subst, cstrs))
    (subst, noneqs) partition
  in
  let constraints = remove_trivial_constraints 
    (Constraint.union eqs (subst_univs_level_constraints subst noneqs))
  in
  (* We remove constraints that are redundant because of the algebraic
     substitution. *)
  let constraints = 
    Constraint.fold (fun (l,d,r as cstr) csts -> 
      if List.mem_assoc l ussubst || List.mem_assoc r ussubst then csts
      else Constraint.add cstr csts)
    constraints Constraint.empty
  in
  let usalg, usnonalg = 
    List.partition (fun (u, _) -> LSet.mem u algs) ussubst
  in
  let remove_same s =
    LMap.fold (fun u v acc ->
      if eq_levels u v then acc
      else LMap.add u (Universe.make v) acc) s LMap.empty
  in
  let subst = 
    LMap.union (LMap.union substdef (remove_same subst))
      (Univ.LMap.of_list usalg)
  in
  let substref = ref subst in
  let norm = normalize_univ_variable_subst substref in
  let _normalize_subst = LMap.iter (fun u v -> ignore(norm u)) subst in
  let subst = !substref in
  let ctx' = LSet.diff ctx (LMap.universes subst) in
  let constraints' =
    (** Residual constraints that can't be normalized further. *)
    List.fold_left (fun csts (u,v) -> 
      enforce_leq v (Universe.make u) csts)
      constraints usnonalg
  in
    (subst, (ctx', constraints'))

