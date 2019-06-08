(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ
open Term
open Constr
open Declarations
open Environ
open Entries
open Type_errors
open Context.Rel.Declaration

(** Check name unicity.
    Redundant with safe_typing's add_field checks -> to remove?. *)

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names =
  let rec check idset = function
    | [] -> idset
    | c::cl ->
        if Id.Set.mem c idset then
          raise (InductiveError (SameNamesConstructors c))
        else
          check (Id.Set.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds ->
        let id = ind.mind_entry_typename in
        let cl = ind.mind_entry_consnames in
        if Id.Set.mem id indset then
          raise (InductiveError (SameNamesTypes id))
        else
          let cstset' = check_constructors_names cstset cl in
          check (Id.Set.add id indset) cstset' inds
  in
  check Id.Set.empty Id.Set.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)


(************************************************************************)
(************************** Cumulativity checking************************)
(************************************************************************)

(* Check arities and constructors *)
let check_subtyping_arity_constructor env subst arcn numparams is_arity =
  let numchecked = ref 0 in
  let basic_check ev tp =
    if !numchecked < numparams then () else Reduction.conv_leq ev tp (subst tp);
    numchecked := !numchecked + 1
  in
  let check_typ typ typ_env =
    match typ with
    | LocalAssum (_, typ') ->
      begin
       try
          basic_check typ_env typ'; Environ.push_rel typ typ_env
        with Reduction.NotConvertible ->
          CErrors.anomaly ~label:"bad inductive subtyping relation"
            Pp.(str "Invalid subtyping relation")
      end
    | _ -> CErrors.anomaly Pp.(str "")
  in
  let typs, codom = Reduction.dest_prod env arcn in
  let last_env = Context.Rel.fold_outside check_typ typs ~init:env in
  if not is_arity then basic_check last_env codom else ()

let check_cumulativity univs variances env_ar params data =
  let uctx = match univs with
    | Monomorphic_entry _ -> raise (InductiveError BadUnivs)
    | Polymorphic_entry (_,uctx) -> uctx
  in
  let instance = UContext.instance uctx in
  if Instance.length instance != Array.length variances then raise (InductiveError BadUnivs);
  let numparams = Context.Rel.nhyps params in
  let new_levels = Array.init (Instance.length instance)
      (fun i -> Level.(make (UGlobal.make DirPath.empty i)))
  in
  let lmap = Array.fold_left2 (fun lmap u u' -> LMap.add u u' lmap)
      LMap.empty (Instance.to_array instance) new_levels
  in
  let dosubst = Vars.subst_univs_level_constr lmap in
  let instance_other = Instance.of_array new_levels in
  let constraints_other = Univ.subst_univs_level_constraints lmap (UContext.constraints uctx) in
  let uctx_other = Univ.UContext.make (instance_other, constraints_other) in
  let env = Environ.push_context uctx_other env_ar in
  let subtyp_constraints =
    Univ.enforce_leq_variance_instances variances
      instance instance_other
      Constraint.empty
  in
  let env = Environ.add_constraints subtyp_constraints env in
  (* process individual inductive types: *)
  List.iter (fun (arity,lc) ->
        check_subtyping_arity_constructor env dosubst arity numparams true;
        Array.iter (fun cnt -> check_subtyping_arity_constructor env dosubst cnt numparams false) lc)
    data

(************************************************************************)
(************************** Type checking *******************************)
(************************************************************************)

type univ_info = { ind_squashed : bool; ind_has_relevant_arg : bool;
                   ind_min_univ : Universe.t option; (* Some for template *)
                   ind_univ : Universe.t }

let check_univ_leq ?(is_real_arg=false) env u info =
  let ind_univ = info.ind_univ in
  let info = if not info.ind_has_relevant_arg && is_real_arg && not (Univ.Universe.is_sprop u)
    then {info with ind_has_relevant_arg=true}
    else info
  in
  (* Inductive types provide explicit lifting from SProp to other universes, so allow SProp <= any. *)
  if type_in_type env || Univ.Universe.is_sprop u || UGraph.check_leq (universes env) u ind_univ
  then { info with ind_min_univ = Option.map (Universe.sup u) info.ind_min_univ }
  else if is_impredicative_univ env ind_univ
  then if Option.is_empty info.ind_min_univ then { info with ind_squashed = true }
    else raise (InductiveError BadUnivs)
  else raise (InductiveError BadUnivs)

let check_context_univs ~ctor ?template env info ctx =
  let check_one d (info,env) =
    let info = match d with
      | LocalAssum (_,t) ->
        (* could be retyping if it becomes available in the kernel *)
        let tj = Typeops.infer_type env t in
        let uj = Sorts.univ_of_sort tj.utj_type in
        let uj =
          match template with
          | Some (_ctx, _levels, (lsubst, _invlsubst)) -> Univ.subst_univs_level_universe lsubst uj
          | None -> uj
        in
        check_univ_leq ~is_real_arg:ctor env uj info
      | LocalDef _ -> info
    in
    info, push_rel d env
  in
  fst (Context.Rel.fold_outside ~init:(info,env) check_one ctx)

let check_indices_matter env_params info indices =
  if not (indices_matter env_params) then info
  else check_context_univs ~ctor:false env_params info indices

(* env_ar contains the inductives before the current ones in the block, and no parameters *)
let check_arity ?template env_params env_ar ind =
  let {utj_val=arity;utj_type=_} = Typeops.infer_type env_params ind.mind_entry_arity in
  let indices, ind_sort = Reduction.dest_arity env_params arity in
  let ind_min_univ, arity, sort =
    match template with
    | Some (_levels, (lsubst, _invlsubst)) ->
      (** Make the parameterized sort *)
      let sort = Univ.subst_univs_level_universe lsubst (Sorts.univ_of_sort ind_sort) in
      let arity = it_mkProd_or_LetIn (mkSort (Sorts.sort_of_univ sort)) indices in
      Some Universe.type0m, arity, sort
    | None -> None, arity, Sorts.univ_of_sort ind_sort
  in
  let univ_info = {
    ind_squashed=false;
    ind_has_relevant_arg=false;
    ind_min_univ;
    ind_univ=sort;
  }
  in
  let univ_info = check_indices_matter env_params univ_info indices in
  (* We do not need to generate the universe of the arity with params;
     if later, after the validation of the inductive definition,
     full_arity is used as argument or subject to cast, an upper
     universe will be generated *)
  let arity = it_mkProd_or_LetIn arity (Environ.rel_context env_params) in
  let x = Context.make_annot (Name ind.mind_entry_typename) (Sorts.relevance_of_sort ind_sort) in
  push_rel (LocalAssum (x, arity)) env_ar,
  (arity, indices, univ_info)

let check_constructor_univs ?template env_ar_par info (args,_) =
  (* We ignore the output, positivity will check that it's the expected inductive type *)
  check_context_univs ~ctor:true ?template env_ar_par info args

let check_constructors ?template env_ar_par isrecord params lc (arity,indices,univ_info) =
  let lc = Array.map_of_list (fun c ->
      let c =
        match template with
        | Some (_ctx, _levels, (lsubst, _invlsubst)) ->
          Vars.subst_univs_level_constr lsubst c
        | None -> c
      in
      (Typeops.infer_type env_ar_par c).utj_val) lc
  in
  let splayed_lc = Array.map (Reduction.dest_prod_assum env_ar_par) lc in
  let univ_info = match Array.length lc with
    (* Empty type: all OK *)
    | 0 -> univ_info

    (* SProp primitive records are OK, if we squash and become fakerecord also OK *)
    | 1 when isrecord -> univ_info

    (* Unit and identity types must squash if SProp *)
    | 1 -> check_univ_leq env_ar_par Univ.Universe.type0m univ_info

    (* More than 1 constructor: must squash if Prop/SProp *)
    | _ -> check_univ_leq env_ar_par Univ.Universe.type0 univ_info
  in
  let univ_info = Array.fold_left (check_constructor_univs ?template env_ar_par) univ_info splayed_lc in
  (* generalize the constructors over the parameters *)
  let lc = Array.map (fun c -> Term.it_mkProd_or_LetIn c params) lc in
  (arity, lc), (indices, splayed_lc), univ_info

let check_record data =
  List.for_all (fun (_,(_,splayed_lc),info) ->
      (* records must have all projections definable -> equivalent to not being squashed *)
      not info.ind_squashed
      (* relevant records must have at least 1 relevant argument *)
      && (Univ.Universe.is_sprop info.ind_univ
          || info.ind_has_relevant_arg)
      && (match splayed_lc with
          (* records must have 1 constructor with at least 1 argument, and no anonymous fields *)
          | [|ctx,_|] ->
            let module D = Context.Rel.Declaration in
            List.exists D.is_local_assum ctx &&
            List.for_all (fun d -> not (D.is_local_assum d)
                                   || not (Name.is_anonymous (D.get_name d)))
              ctx
          | _ -> false))
    data

(* Allowed eliminations *)

(* Previous comment: *)
(* Unitary/empty Prop: elimination to all sorts are realizable *)
(* unless the type is large. If it is large, forbids large elimination *)
(* which otherwise allows simulating the inconsistent system Type:Type. *)
(* -> this is now handled by is_smashed: *)
(* - all_sorts in case of small, unitary Prop (not smashed) *)
(* - logical_sorts in case of large, unitary Prop (smashed) *)

let allowed_sorts {ind_squashed;ind_univ;ind_min_univ=_;ind_has_relevant_arg=_} =
  if not ind_squashed then InType
  else Sorts.family (Sorts.sort_of_univ ind_univ)

(* [lower_ctx params] Returns the list [x_1, ..., x_n] of levels
   contributing to template polymorphism. The elements x_k is None if
   the k-th parameter (starting from the most oldest and ignoring
   let-definitions) is not contributing or is Some u_k if its level is
   u_k and is contributing.

   For a level to be template polymorphic, it must be a level variable
   [l] appearing as the conclusion of a parameter type.  It must not be
   constrained from below, so any universe [l' <= l] can be used as an
   instance of [l]. All bounds from above, i.e.  [l <=/< r] will be
   valid for any [l' <= l]. We check this by typechecking a generalized
   version of the inductive declaration for fresh l', represented as
   [Var i] universe levels.

   [lower_ctx] hence also returns a substitution [x_i -> Level.Var i]
   and extension of the universe context for [Prop <= Var i]
   universes. A template-polymorphic inductive must be typable for *any*
   instantiation of its universes, so we check typability of the
   constructors under this substitution for the parameters and arities. *)
let lower_ctx paramsctxt =
  let fold decl ((lsubst, invlsubst) as subst, levels, params', uctx) =
    match decl with
    | (LocalAssum (_, p)) ->
      (let ctx, ty = Term.decompose_prod_assum p in
      match kind ty with
        | Sort (Type u) ->
          (match Univ.Universe.level u with
          | Some l ->
            let subst, uctx, ty =
              try
                let l' = Univ.LMap.find l lsubst in
                (subst, uctx, it_mkProd_or_LetIn (mkType (Univ.Universe.make l')) ctx)
              with Not_found ->
                let l' = Univ.Level.var (Univ.LMap.cardinal lsubst) in
                let lsubst = Univ.LMap.add l l' lsubst in
                let invlsubst = Univ.LMap.add l' l invlsubst in
                let uctx = Univ.ContextSet.add_universe l' uctx in
                let cstr = Univ.enforce_leq_level l' l Univ.Constraint.empty in
                let uctx = Univ.ContextSet.add_constraints cstr uctx in
                ((lsubst, invlsubst), uctx, it_mkProd_or_LetIn (mkType (Univ.Universe.make l')) ctx)
            in (subst, Some l :: levels, Context.Rel.Declaration.set_type ty decl :: params', uctx)
          | None -> (subst, None :: levels, decl :: params', uctx))
        | _ -> (subst, None :: levels, decl :: params', uctx))
    | LocalDef _ -> (subst, levels, decl :: params', uctx)
  in
  let subst, levels, params', uctx =
    List.fold_right fold paramsctxt ((Univ.LMap.empty, Univ.LMap.empty), [], [], Univ.ContextSet.empty) in
  (subst, List.rev levels, params', uctx)

let abstract_packets ?template_info usubst ((arity,lc),(indices,splayed_lc),univ_info) =
  let arity = Vars.subst_univs_level_constr usubst arity in
  let lc = Array.map (Vars.subst_univs_level_constr usubst) lc in
  let indices = Vars.subst_univs_level_context usubst indices in
  let splayed_lc = Array.map (fun (args,out) ->
      let args = Vars.subst_univs_level_context usubst args in
      let out = Vars.subst_univs_level_constr usubst out in
      args,out)
      splayed_lc
  in
  let ind_univ = Univ.subst_univs_level_universe usubst univ_info.ind_univ in

  let arity =
    match template_info with
    | Some levels ->
      (* Invariant: always there for template polymorphic inductives *)
      let min_univ = Option.get univ_info.ind_min_univ in
      (* Go back to the fixed universes *)
      let min_univ = Univ.subst_univs_level_universe usubst min_univ in
      TemplateArity {template_param_levels=levels; template_level=min_univ}
    | None -> RegularArity {mind_user_arity=arity;mind_sort=Sorts.sort_of_univ ind_univ}
  in

  let kelim = allowed_sorts univ_info in
  (arity,lc), (indices,splayed_lc), kelim

let typecheck_inductive env (mie:mutual_inductive_entry) =
  let () = match mie.mind_entry_inds with
  | [] -> CErrors.anomaly Pp.(str "empty inductive types declaration.")
  | _ -> ()
  in
  (* Check unicity of names (redundant with safe_typing's add_field checks) *)
  mind_check_names mie;
  assert (List.is_empty (Environ.rel_context env));

  let has_template_poly = List.exists (fun oie -> oie.mind_entry_template) mie.mind_entry_inds in

  (* universes *)
  let env_univs, template_info =
    match mie.mind_entry_universes with
    | Monomorphic_entry ctx ->
      if has_template_poly then
        let env = set_universes_lbound env Univ.Level.prop in
        push_context_set ctx env, Some ctx
      else push_context_set ctx env, None
    | Polymorphic_entry (_, ctx) ->
      if has_template_poly then
        CErrors.anomaly ~label:"polymorphic_template_ind"
          Pp.(strbrk "Template polymorphism and full polymorphism are incompatible.");
      push_context ctx env, None
  in

  (* Params *)
  let env_params, params = Typeops.check_context env_univs mie.mind_entry_params in

  (* Arities *)
  let params, env_ar, template, data =
    match template_info with
    | Some ctx ->
      (** Check that using unconstrained universes for the template polymorphic ones
          allow to typecheck the declaration. *)
      let subst, levels, params, ctx' = lower_ctx params in
      (** We push a relaxed universe context where each template-polymorphic universe [l]
          has a corresponding relaxed one Prop <= (Var i) <= l.
          Typechecking only does checking of universes, so it ensures that [Var i = l]
          is a valid instantiation (otherwise said, typechecking will fail if it encounters
          [Var i < l]). *)
      let env_univs = push_context_set ctx' env_univs in
      (** Check that the relaxed context typechecks *)
      let env_params, params = Typeops.check_context env_univs params in
      (** Check that the relaxed arity typechecks (substituting _only_ in the conclusion of the arity) *)
      let env_ar, data = List.fold_left_map (check_arity env_params ~template:(levels, subst))
          env_univs mie.mind_entry_inds in
      params, env_ar, Some (ctx, levels, subst), data
    | None ->
      let env_ar, data = List.fold_left_map (check_arity env_params) env_univs mie.mind_entry_inds in
      params, env_ar, None, data
  in

  let env_ar_par = push_rel_context params env_ar in

  (* Constructors *)
  let isrecord = match mie.mind_entry_record with
    | Some (Some _) -> true
    | Some None | None -> false
  in
  let data = List.map2 (fun ind data ->
      check_constructors ?template env_ar_par isrecord params ind.mind_entry_lc data)
      mie.mind_entry_inds data
  in

  let record = mie.mind_entry_record in
  let data, record = match record with
    | None | Some None -> data, record
    | Some (Some _) ->
      if check_record data then
        data, record
      else
        (* if someone tried to declare a record as SProp but it can't
           be primitive we must squash. *)
        let data = List.map (fun (a,b,univs) ->
            a,b,check_univ_leq env_ar_par Univ.Universe.type0m univs)
            data
        in
        data, Some None
  in

  let () = match mie.mind_entry_variance with
    | None -> ()
    | Some variances ->
      check_cumulativity mie.mind_entry_universes variances env_ar params (List.map pi1 data)
  in

  (* Abstract universes *)
  let template_info, (usubst, univs) =
    (* Maybe refactor this *)
    match template with
    | Some (ctx, levels, (_lsubst, invlsubst)) ->
      (** We go back from the relaxed context to the original one,
          effectively performing [Var i = l] for each template-polymorphic universe [l]. *)
      Some levels, (invlsubst, Monomorphic ctx)
    | None ->
      None, Declareops.abstract_universes mie.mind_entry_universes
  in
  let params = Vars.subst_univs_level_context usubst params in
  let data = List.map (abstract_packets ?template_info usubst) data in

  let env_ar_par =
    let ctx = Environ.rel_context env_ar_par in
    let ctx = Vars.subst_univs_level_context usubst ctx in
    let env = Environ.pop_rel_context (Environ.nb_rel env_ar_par) env_ar_par in
    Environ.push_rel_context ctx env
  in

  env_ar_par, univs, mie.mind_entry_variance, record, params, Array.of_list data
