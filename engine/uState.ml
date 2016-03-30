(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Univ
       
module StringOrd = struct type t = string let compare = String.compare end
module UNameMap = struct
    
  include Map.Make(StringOrd)
    
  let union s t = 
    if s == t then s
    else
      merge (fun k l r -> 
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t
end

type uinfo = {
  uname : string option;
  uloc : Loc.t option;
}

(* 2nd part used to check consistency on the fly. *)
type t =
 { uctx_names : LevelName.t UNameMap.t * uinfo LMap.t;
   uctx_local : ContextSet.t; (** The local context of variables *)
   uctx_univ_variables : Universes.universe_opt_subst;
   (** The local universes that are unification variables *)
   uctx_univ_algebraic : universe_set; 
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   uctx_universes : UGraph.t; (** The current graph extended with the local constraints *)
   uctx_initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
 }
  
let empty =
  { uctx_names = UNameMap.empty, LMap.empty;
    uctx_local = ContextSet.empty;
    uctx_univ_variables = LMap.empty;
    uctx_univ_algebraic = LSet.empty;
    uctx_universes = UGraph.initial_universes;
    uctx_initial_universes = UGraph.initial_universes }

let make u =
    { empty with 
      uctx_universes = u; uctx_initial_universes = u}

let is_empty ctx =
  ContextSet.is_empty ctx.uctx_local && 
    LMap.is_empty ctx.uctx_univ_variables

let union ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty ctx' then ctx
  else
    let local = ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let names = UNameMap.union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
    let newus = LSet.diff (ContextSet.levels ctx'.uctx_local)
                               (ContextSet.levels ctx.uctx_local) in
    let newus = LSet.diff newus (LMap.domain ctx.uctx_univ_variables) in
    let declarenew g =
      LSet.fold (fun u g -> UGraph.add_universe u false g) newus g
    in
    let names_rev = LMap.union (snd ctx.uctx_names) (snd ctx'.uctx_names) in
      { uctx_names = (names, names_rev);
        uctx_local = local;
        uctx_univ_variables = 
          LMap.subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
        uctx_univ_algebraic = 
          LSet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
        uctx_initial_universes = declarenew ctx.uctx_initial_universes;
        uctx_universes = 
          if local == ctx.uctx_local then ctx.uctx_universes
          else
            let cstrsr = ContextSet.constraints ctx'.uctx_local in
              UGraph.merge_constraints cstrsr (declarenew ctx.uctx_universes) }

let context_set ctx = ctx.uctx_local

let constraints ctx = snd ctx.uctx_local

let context ctx = ContextSet.to_context ctx.uctx_local

let of_context_set ctx = { empty with uctx_local = ctx }

let subst ctx = ctx.uctx_univ_variables

let ugraph ctx = ctx.uctx_universes

let algebraics ctx = ctx.uctx_univ_algebraic

let constrain_variables diff ctx =
  LSet.fold
    (fun l cstrs ->
      try
        match LMap.find l ctx.uctx_univ_variables with
        | Some u -> Constraint.add (Level.make l, Eq,
                                        Option.get (Universe.level u)) cstrs
        | None -> cstrs
      with Not_found | Option.IsNone -> cstrs)
    diff Constraint.empty

let add_uctx_names ?loc s l (names, names_rev) =
  (UNameMap.add s l names, LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, LMap.add l { uname = None; uloc = loc } names_rev)

let of_binders b =
  let ctx = empty in
  let names =
    List.fold_left (fun acc (id, l) -> add_uctx_names (Id.to_string id) l acc)
                   ctx.uctx_names b
  in { ctx with uctx_names = names }

let instantiate_variable l b v =
  try v := LMap.update l (Some b) !v
  with Not_found -> assert false

exception UniversesDiffer

let process_universe_constraints ctx cstrs =
  let open Univ in
  let univs = ctx.uctx_universes in
  let vars = ref ctx.uctx_univ_variables in
  let normalize = Universes.normalize_universe_opt_subst vars in
  let rec unify_universes fo l d r local =
    let l = normalize l and r = normalize r in
      if Universe.equal l r then local
      else 
        let varinfo x = 
          match Universe.level x with
          | Some (l,0) -> Inr (l, LMap.mem l !vars,
                              LSet.mem l ctx.uctx_univ_algebraic)
          | _ -> Inl x
        in
          if d == Universes.ULe then
            if UGraph.check_leq univs l r then
              (** Keep Prop/Set <= var around if var might be instantiated by prop or set
                  later. *)
              if Universe.is_level l then 
                match Universe.level r with
                | Some r ->
                  Constraint.add (Option.get (Universe.level l),Le,r) local
                | _ -> local
              else local
            else
              match Universe.level r with
              | None -> Constraint.enforce (l,Le,r) local
              | Some rl ->
                if Level.is_small rl then
                  let levels = Universe.level_set l in
                    LSet.fold (fun l local ->
                      if LevelName.is_small l || LMap.mem l !vars then
                        unify_universes fo (Universe.make_name l)
                                        Universes.UEq r local
                      else
                        raise (UniverseInconsistency
                                 (Le, Universe.make_name l, r, None)))
                      levels local
                else
                  Constraint.enforce_leq l r local
          else if d == Universes.ULub then
            match varinfo l, varinfo r with
            | (Inr (l', true, _), Inr (r', _, _)) 
            | (Inr (r', _, _), Inr (l', true, _)) -> 
              instantiate_variable l' (Universe.make_name r') vars; 
              Constraint.enforce_eq l r local
            | _, _ ->
               unify_universes true l Universes.UEq r local
          else (* d = Universes.UEq *)
            match varinfo l, varinfo r with
            | Inr (l', lloc, _), Inr (r', rloc, _) ->
              let () = 
                if lloc then
                  instantiate_variable l' r vars
                else if rloc then 
                  instantiate_variable r' l vars
                else if not (UGraph.check_eq univs l r) then
                  (* Two rigid/global levels, none of them being local,
                     one of them being Prop/Set, disallow *)
                  if LevelName.is_small l' || LevelName.is_small r' then
                    raise (UniverseInconsistency (Eq, l, r, None))
                  else
                    if fo then 
                      raise UniversesDiffer
              in
                Constraint.enforce_eq l r local
            | Inr (l, loc, alg), Inl r
            | Inl r, Inr (l, loc, alg) ->
               let inst = univ_level_rem (l,0) r r in
               (* if alg then *) (instantiate_variable l inst vars; local)
               (* else *)
               (*   let lu = Universe.make_name l in *)
               (*   if univ_level_mem (l,0) r then *)
               (*     Constraint.enforce_leq inst lu local *)
               (*   else raise (UniverseInconsistency (Eq, lu, r, None)) *)
            | _, _ (* One of the two is algebraic or global *) -> 
             if UGraph.check_eq univs l r then local
             else raise (UniverseInconsistency (Eq, l, r, None))
  in
  let local = 
    Universes.Constraints.fold (fun (l,d,r) local -> unify_universes false l d r local)
      cstrs Constraint.empty
  in
    !vars, local

let add_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let cstrs' = Constraint.fold (fun (l,d,r) acc -> 
    let l = Universe.make l and r = Universe.make r in
    let cstr' = 
      if d == Lt then (Universe.super l, Universes.ULe, r)
      else (l, (if d == Le then Universes.ULe else Universes.UEq), r)
    in Universes.Constraints.add cstr' acc)
    cstrs Universes.Constraints.empty
  in
  let vars, local' = process_universe_constraints ctx cstrs' in
    { ctx with uctx_local = (univs, Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes }

(* let addconstrkey = Profile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = Profile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let vars, local' = process_universe_constraints ctx cstrs in
    { ctx with uctx_local = (univs, Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes }

let pr_uctx_level uctx = 
  let map, map_rev = uctx.uctx_names in 
    fun l ->
      try str (Option.get (LMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        Universes.pr_with_global_universes l

let universe_context ?names ctx =
  match names with
  | None -> [], ContextSet.to_context ctx.uctx_local
  | Some pl ->
     let levels = ContextSet.levels ctx.uctx_local in
     let newinst, map, left =
       List.fold_right
         (fun (loc,id) (newinst, map, acc) ->
          let l =
            try UNameMap.find (Id.to_string id) (fst ctx.uctx_names)
            with Not_found ->
              user_err_loc (loc, "universe_context",
                            str"Universe " ++ Nameops.pr_id id ++ str" is not bound anymore.")
          in (l :: newinst, (id, l) :: map, LSet.remove l acc))
         pl ([], [], levels)
     in
       if not (LSet.is_empty left) then
         let n = LSet.cardinal left in
         let loc =
          let get_loc u = try (LMap.find u (snd ctx.uctx_names)).uloc with Not_found -> None in
          try List.find_map get_loc (LSet.elements left) with Not_found -> Loc.ghost
         in
           user_err_loc (loc, "universe_context",
                        (str(CString.plural n "Universe") ++ spc () ++
                             LSet.pr (pr_uctx_level ctx) left ++
                             spc () ++ str (CString.conjugate_verb_to_be n) ++ str" unbound."))
      else
        let ctx =
          UContext.make (Abstraction.of_array (Array.of_list newinst),
                              ContextSet.constraints ctx.uctx_local)
        in map, ctx

let restrict ctx vars =
  let uctx' = Universes.restrict_universe_context ctx.uctx_local vars in
  { ctx with uctx_local = uctx' }

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let merge ?loc sideff rigid uctx ctx' =
  let open Univ in
  let levels = ContextSet.levels ctx' in
  let uctx = if sideff then uctx else
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let fold u accu =
        if LMap.mem u accu then accu
        else LMap.add u None accu
      in
      let uvars' = LSet.fold fold levels uctx.uctx_univ_variables in
        if b then
          { uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = LSet.union uctx.uctx_univ_algebraic levels }
        else { uctx with uctx_univ_variables = uvars' }
  in
  let uctx_local =
    if sideff then uctx.uctx_local
    else ContextSet.append ctx' uctx.uctx_local
  in
  let declare g =
    LSet.fold (fun u g ->
               try UGraph.add_universe u false g
               with UGraph.AlreadyDeclared when sideff -> g)
              levels g
  in
  let uctx_names =
    let fold u accu =
      let modify _ info = match info.uloc with
      | None -> { info with uloc = loc }
      | Some _ -> info
      in
      try LMap.modify u modify accu
      with Not_found -> LMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.uctx_names, LSet.fold fold levels (snd uctx.uctx_names))
  in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare uctx.uctx_universes in
  let uctx_universes = UGraph.merge_constraints (ContextSet.constraints ctx') univs in
    { uctx with uctx_names; uctx_local; uctx_universes; uctx_initial_universes = initial }

let merge_subst uctx s =
  { uctx with uctx_univ_variables = LMap.subst_union uctx.uctx_univ_variables s }

let emit_side_effects eff u =
  let uctxs = Safe_typing.universes_of_private eff in
  List.fold_left (merge true univ_rigid) u uctxs

let new_univ_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level (Global.current_dirpath ()) in
  let ctx' = ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b -> 
      let uvars' = LMap.add u None uvars in
        if b then {uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = LSet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars'}, false
  in
  let names = 
    match name with
    | Some n -> add_uctx_names ?loc n u uctx.uctx_names
    | None -> add_uctx_loc u loc uctx.uctx_names
  in
  let initial =
    UGraph.add_universe u false uctx.uctx_initial_universes
  in                                                 
  let uctx' =
    {uctx' with uctx_names = names; uctx_local = ctx';
                uctx_universes = UGraph.add_universe u false uctx.uctx_universes;
                uctx_initial_universes = initial}
  in uctx', Level.make u

let add_global_univ uctx u =
  let initial =
    UGraph.add_universe u true uctx.uctx_initial_universes
  in
  let univs = 
    UGraph.add_universe u true uctx.uctx_universes
  in
  { uctx with uctx_local = ContextSet.add_universe u uctx.uctx_local;
                                     uctx_initial_universes = initial;
                                     uctx_universes = univs }

let make_flexible_variable ctx b u =
  let {uctx_univ_variables = uvars; uctx_univ_algebraic = avars} = ctx in
  let uvars' = LMap.add u None uvars in
  let avars' = 
    if b then
      let uu = Universe.make_name u in
      let substu_not_alg u' v =
        Option.cata (fun vu -> Universe.equal uu vu && not (LSet.mem u' avars)) false v
      in
        if not (LMap.exists substu_not_alg uvars)
        then LSet.add u avars else avars 
    else avars 
  in
  {ctx with uctx_univ_variables = uvars'; 
      uctx_univ_algebraic = avars'}

let is_sort_variable uctx s = 
  match s with 
  | Sorts.Type u -> 
    (match Universe.level_name u with
    | Some l as x -> 
        if LSet.mem l (ContextSet.levels uctx.uctx_local) then x
        else None
    | None -> None)
  | _ -> None

let subst_univs_context_with_def def usubst (ctx, cst) =
  (LSet.diff ctx def, subst_univs_constraints usubst cst)

let normalize_variables uctx =
  let normalized_variables, undef, def, subst = 
    Universes.normalize_univ_variables uctx.uctx_univ_variables 
  in
  let ctx_local = subst_univs_context_with_def def (make_subst subst) uctx.uctx_local in
  let ctx_local', univs = Universes.refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

let abstract_undefined_variables uctx =
  let vars' = 
    LMap.fold (fun u v acc ->
      if v == None then LSet.remove u acc
      else acc)
    uctx.uctx_univ_variables uctx.uctx_univ_algebraic
  in { uctx with uctx_local = ContextSet.empty;
      uctx_univ_algebraic = vars' }

let fix_undefined_variables uctx =
  let algs', vars' = 
    LMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (LSet.remove u algs, LMap.remove u vars)
      else acc)
      uctx.uctx_univ_variables 
      (uctx.uctx_univ_algebraic, uctx.uctx_univ_variables)
  in
  { uctx with uctx_univ_variables = vars';
    uctx_univ_algebraic = algs' }

let refresh_undefined_univ_variables uctx =
  let subst, ctx' = Universes.fresh_universe_context_set_instance uctx.uctx_local in
  let alg =
    LSet.fold
      (fun u acc -> LSet.add
                   (subst_univs_level_level_name subst u) acc) 
      uctx.uctx_univ_algebraic LSet.empty 
  in
  let vars = 
    LMap.fold
      (fun u v acc ->
        LMap.add (subst_univs_level_level_name subst u) 
          (Option.map (subst_univs_level_universe subst) v) acc)
      uctx.uctx_univ_variables LMap.empty
  in
  let declare g = LSet.fold (fun u g -> UGraph.add_universe u false g)
                                   (ContextSet.levels ctx') g in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare UGraph.initial_universes in
  let uctx' = {uctx_names = uctx.uctx_names;
               uctx_local = ctx'; 
               uctx_univ_variables = vars; uctx_univ_algebraic = alg;
               uctx_universes = univs;
               uctx_initial_universes = initial } in
    uctx', subst

let normalize uctx = 
  let ((vars',algs'), us') = 
    Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
				    uctx.uctx_univ_algebraic
  in
  if ContextSet.equal us' uctx.uctx_local then uctx
  else
    let us', universes =
      Universes.refresh_constraints uctx.uctx_initial_universes us'
    in
    { uctx_names = uctx.uctx_names;
      uctx_local = us'; 
      uctx_univ_variables = vars'; 
      uctx_univ_algebraic = algs';
      uctx_universes = universes;
      uctx_initial_universes = uctx.uctx_initial_universes }

let universe_of_name uctx s = 
  UNameMap.find s (fst uctx.uctx_names)

let add_universe_name uctx s l =
  let names' = add_uctx_names s l uctx.uctx_names in
  { uctx with uctx_names = names' }

let update_sigma_env uctx env =
  let univs = Environ.universes env in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge true univ_rigid eunivs eunivs.uctx_local
