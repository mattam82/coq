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
  
(** Precondition: flexible <= ctx *)
let choose_canonical ctx flexible s =
  let global = LSet.diff s ctx in
  let flexible, rigid = LSet.partition (fun x -> LMap.mem x flexible) (LSet.inter s ctx) in
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
	  
let make_opt_subst s = 
  fun x -> 
    (match Univ.LMap.find x s with
    | Some u -> u
    | None -> raise Not_found)

let subst_opt_univs_constr s = 
  let f = make_opt_subst s in
    subst_univs_fn_constr f

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

let is_defined_var u l = 
  try
    match LMap.find u l with
    | Some _ -> true
    | None -> false
  with Not_found -> false

let subst_univs_subst u l s = 
  LMap.add u l s
    
exception Found of Level.t
let find_inst insts v =
  try LMap.iter (fun k (enf,alg,v') ->
    if not alg && enf && Universe.eq v' v then raise (Found k))
	insts; raise Not_found
  with Found l -> l

let add_inst u (enf,b,lbound) insts =
  match lbound with
  | Some v -> LMap.add u (enf,b,v) insts
  | None -> insts

exception Stays

let compute_lbound left =
 (** The universe variable was not fixed yet.
     Compute its level using its lower bound. *)
  if left = [] then None
  else
    let lbound = List.fold_left (fun lbound (d, l) -> 
      if d = Le (* l <= ?u *) then (Universe.sup l lbound)
      else (* l < ?u *) 
	(assert (d = Lt); 
	 (Universe.sup (Universe.super l) lbound)))	    
      Universe.type0m left
    in 
      Some lbound
  
let maybe_enforce_leq lbound u cstrs = 
  match lbound with
  | Some lbound -> enforce_leq lbound (Universe.make u) cstrs
  | None -> cstrs

let instantiate_with_lbound u lbound alg enforce (ctx, us, insts, cstrs) =
  if enforce then
    let inst = Universe.make u in
    let cstrs' = enforce_leq lbound inst cstrs in
      (ctx, us, LMap.add u (enforce,alg,lbound) insts, cstrs'), (enforce, alg, inst)
  else (* Actually instantiate *)
    (Univ.LSet.remove u ctx, Univ.LMap.add u (Some lbound) us, 
     LMap.add u (enforce,alg,lbound) insts, cstrs), (enforce, alg, lbound)
	
let minimize_univ_variables ctx us algs left right cstrs =
  let left, lbounds = 
    Univ.LMap.fold (fun r lower (left, lbounds as acc)  ->
      if Univ.LMap.mem r us then acc
      else (* Fixed universe, just compute its glb for sharing *)
	let lbounds' = 
	  match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
	  | None -> lbounds
	  | Some lbound -> LMap.add r (true, false, lbound) lbounds
	in (Univ.LMap.remove r left, lbounds'))
      left (left, Univ.LMap.empty)
  in
  let rec instance (ctx', us, insts, cstrs as acc) u =
    let acc, left = 
      try let l = LMap.find u left in
	    List.fold_left (fun (acc, left') (d, l) -> 
	      let acc', (enf,alg,l') = aux acc l in
		assert(not alg);
		let l' = 
		  if enf then Universe.make l 
		  else match Universe.level l' with Some _ -> l' | None -> Universe.make l 
		in
		  acc', (d, l') :: left') (acc, []) l
      with Not_found -> acc, []
    and right =
      try Some (LMap.find u right)
      with Not_found -> None
    in
    let instantiate_lbound lbound =
      if LSet.mem u algs && right = None then
	 (* u is algebraic and has no upper bound constraints: we
	    instantiate it with it's lower bound, if any *)
	 instantiate_with_lbound u lbound true false acc
      else (* u is non algebraic *)
	match Universe.level lbound with
	| Some l -> (* The lowerbound is directly a level *) 
	  (* u is not algebraic but has no upper bounds,
	     we instantiate it with its lower bound if it is a 
	     different level, otherwise we keep it. *)
	  if not (Level.eq l u) then
	    instantiate_with_lbound u lbound false false acc
	  else acc, (true, false, lbound)
	| None -> 
	  try 
	    (* Another universe represents the same lower bound, 
	       we can share them with no harm. *)
	    let can = find_inst insts lbound in
	      instantiate_with_lbound u (Universe.make can) false false acc
	  with Not_found -> 
	    (* We set u as the canonical universe representing lbound *)
	    instantiate_with_lbound u lbound false true acc
    in
    let lbound = compute_lbound left in
      match lbound with
      | None -> (* Nothing to do *)
	acc, (true, false, Universe.make u)
      | Some lbound ->
	instantiate_lbound lbound
  and aux (ctx', us, seen, cstrs as acc) u =
    try acc, LMap.find u seen 
    with Not_found ->
      let acc, inst = instance acc u in
	(acc, inst)
  in
    LMap.fold (fun u v (ctx', us, seen, cstrs as acc) -> 
      if v = None then fst (aux acc u)
      else LSet.remove u ctx', us, seen, cstrs)
      us (ctx, us, lbounds, cstrs)
      
    
    (* LMap.fold (fun u v (ctx', us, insts, cstrs as acc) ->  *)
    (* if v = None then *)
    (*   let lbound, lev, hasup =  *)
    (* 	instantiate_univ_variables insts ucstrsl ucstrsr u cstrs *)
    (*   in *)
    (* 	    match hasup with *)
    (* 	    | Some cstrs' -> *)
    (* 	       (\* We found upper bound constraints, u must be kept *\) *)
    (* 	       instantiate_with_lbound u lbound false true (ctx', us, insts, cstrs') *)
    (* 	    | None -> (\* No upper bounds *\) *)
    (* 	      if Univ.LSet.mem u algs then  *)
    (* 		(\* u is algebraic and has no upper bound constraints: *)
    (* 		   we instantiate it with it's lower bound, if any *\) *)
    (* 		instantiate_with_lbound u lbound true false acc *)
    (* 	      else (\* u is not algebraic but has no upper bounds, *)
    (* 		      we instantiate it with its lower bound if it is a  *)
    (* 		      different level, otherwise we keep it. *\) *)
    (* 		if not (Level.eq lev u) then *)
    (* 		  instantiate_with_lbound u lbound false false acc *)
    (* 		else (\* We couldn't do anything, we can only share us lower bound *\) *)
    (* 		  try let can = find_inst insts lbound in  *)
    (* 		      let ucan = Universe.make can in *)
    (* 			instantiate_with_lbound u (Some ucan) false false acc *)
    (* 		  with Not_found ->  *)
    (* 		    instantiate_with_lbound u lbound false true acc *)
    (* 	else acc *)
    (* else (Univ.LSet.remove u ctx', us, insts, cstrs)) *)
      
let normalize_context_set (ctx, csts) us algs = 
  let uf = UF.create () in
  let csts = 
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = Univ.merge_constraints csts Univ.initial_universes in
      Univ.constraints_of_universes (Univ.normalize_universes g)
  in
  let noneqs =
    Constraint.fold (fun (l,d,r) noneqs ->
      if d = Eq then (UF.union l r uf; noneqs) 
      else Constraint.add (l,d,r) noneqs)
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
  let us = 
    LMap.subst_union (LMap.map (fun v -> Some (Universe.make v)) subst) us
  in
  (* Compute the left and right set of flexible variables, constraints
     mentionning other variables remain in noneqs. *)
  let noneqs, ucstrsl, ucstrsr = 
    Constraint.fold (fun (l,d,r as cstr) (noneq, ucstrsl, ucstrsr) -> 
      let lus = LMap.mem l us 
      and rus = LMap.mem r us
      in
      let ucstrsl' = 
	if lus then add_list_map l (d, r) ucstrsl
	else ucstrsl
      and ucstrsr' = 
	add_list_map r (d, l) ucstrsr
      in 
      let noneqs = 
	if lus || rus then noneq 
	else Constraint.add cstr noneq
      in (noneqs, ucstrsl', ucstrsr'))
    noneqs (empty_constraint, LMap.empty, LMap.empty)
  in
  (* Now we construct the instanciation of each variable. *)
  let ctx', us, inst, noneqs = 
    minimize_univ_variables ctx us algs ucstrsr ucstrsl noneqs
  in
  let us = ref us in
  let norm = normalize_univ_variable_opt_subst us in
  let _normalize_subst = LMap.iter (fun u v -> ignore(norm u)) !us in
    (!us, (ctx', Constraint.union noneqs eqs))

(* let normalize_conkey = Profile.declare_profile "normalize_context_set" *)
(* let normalize_context_set a b c = Profile.profile3 normalize_conkey normalize_context_set a b c *)
