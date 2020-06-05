(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Sorts
open Util
open Context
open Environ
open Names
open Libnames
open Nameops
open Constrexpr
open Constrexpr_ops
open Constrintern
open Type_errors
open Pretyping
open Context.Rel.Declaration
open Entries

module RelDecl = Context.Rel.Declaration

(* 3b| Mutual inductive definitions *)

let warn_auto_template =
  CWarnings.create ~name:"auto-template" ~category:"vernacular" ~default:CWarnings.Disabled
    (fun id ->
       Pp.(strbrk "Automatically declaring " ++ Id.print id ++
           strbrk " as template polymorphic. Use attributes or " ++
           strbrk "disable Auto Template Polymorphism to avoid this warning."))

let should_auto_template =
  let open Goptions in
  let auto = ref true in
  let () = declare_bool_option
      { optdepr  = false;
        optkey   = ["Auto";"Template";"Polymorphism"];
        optread  = (fun () -> !auto);
        optwrite = (fun b -> auto := b); }
  in
  fun id would_auto ->
    let b = !auto && would_auto in
    if b then warn_auto_template id;
    b

let push_types env idl rl tl =
  List.fold_left3 (fun env id r t -> EConstr.push_rel (LocalAssum (make_annot (Name id) r,t)) env)
    env idl rl tl

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

let check_all_names_different indl =
  let ind_names = List.map (fun ind -> ind.ind_name) indl in
  let cstr_names = List.map_append (fun ind -> List.map fst ind.ind_lc) indl in
  let l = List.duplicates Id.equal ind_names in
  let () = match l with
  | [] -> ()
  | t :: _ -> raise (InductiveError (SameNamesTypes t))
  in
  let l = List.duplicates Id.equal cstr_names in
  let () = match l with
  | [] -> ()
  | c :: _ -> raise (InductiveError (SameNamesConstructors (List.hd l)))
  in
  let l = List.intersect Id.equal ind_names cstr_names in
  match l with
  | [] -> ()
  | _ -> raise (InductiveError (SameNamesOverlap l))

(** Make the arity conclusion flexible to avoid generating an upper bound universe now,
    only if the universe does not appear anywhere else.
    This is really a hack to stay compatible with the semantics of template polymorphic
    inductives which are recognized when a "Type" appears at the end of the conlusion in
    the source syntax. *)

let rec check_type_conclusion ind =
  let open Glob_term in
    match DAst.get ind with
    | GSort (UAnonymous {rigid=true}) -> (Some true)
    | GSort (UNamed _) -> (Some false)
    | GProd ( _, _, _, e)
    | GLetIn (_, _, _, e)
    | GLambda (_, _, _, e)
    | GApp (e, _)
    | GCast (e, _) -> check_type_conclusion e
    | _ -> None

let make_anonymous_conclusion_flexible sigma = function
  | None -> sigma
  | Some (false, _) -> sigma
  | Some (true, s) ->
    (match EConstr.ESorts.kind sigma s with
     | Type u ->
       (match Univ.universe_level u with
        | Some u ->
          Evd.make_flexible_variable sigma ~algebraic:true u
        | None -> sigma)
     | _ -> sigma)

let intern_ind_arity env sigma ind =
  let c = intern_gen IsType env sigma ind.ind_arity in
  let impls = Implicit_quantifiers.implicits_of_glob_constr ~with_products:true c in
  let pseudo_poly = check_type_conclusion c in
  (constr_loc ind.ind_arity, c, impls, pseudo_poly)

let pretype_ind_arity env sigma (loc, c, impls, pseudo_poly) =
  let sigma,t = understand_tcc env sigma ~expected_type:IsType c in
  match Reductionops.sort_of_arity env sigma t with
  | exception Invalid_argument _ ->
    user_err ?loc (str "Not an arity")
  | s ->
    let concl = match pseudo_poly with
      | Some b -> Some (b, s)
      | None -> None
    in
    sigma, (t, Retyping.relevance_of_sort s, concl, impls)

(* ind_rel is the Rel for this inductive in the context without params.
   n is how many arguments there are in the constructor.
   nc is how many constructors we passed (they are in the context as well) *)
let model_conclusion env sigma ind_rel params n nc arity_indices =
  let model_head = EConstr.mkRel (n + nc + Context.Rel.length params + ind_rel) in
  let model_params = Context.Rel.to_extended_vect EConstr.mkRel n params in
  let sigma,model_indices =
    List.fold_right
      (fun (_,t) (sigma, subst) ->
        (* t lives in [u_params; ind_0..ind_n-1; params; indices (of size #|subst|)]
           and we want to move it to
           [u_params; ind_0..ind_n-1..ind_k; cstrs; params; args (of size n)]
        *)
        let t = EConstr.Vars.substl subst
          (EConstr.Vars.liftn n (List.length subst + 1)
          (EConstr.Vars.liftn (nc+ind_rel) (List.length params + List.length subst + 1) t)) in
        let sigma, c = Evarutil.new_evar env sigma t in
        sigma, c::subst)
      arity_indices (sigma, []) in
  sigma, EConstr.mkApp (EConstr.mkApp (model_head, model_params), Array.of_list (List.rev model_indices))

let lift_context n ctx =
  let (_, ctx') = List.fold_right
    (fun decl (k, ctx') ->
      (succ k, map_constr (EConstr.Vars.liftn n k) decl :: ctx'))
    ctx (1, [])
  in ctx'

let interp_cstrs (sigma, cenv, ind_rel, ncstrs, lifted_params) impls ind arity =
  let cnames,ctyps = List.split ind.ind_lc in
  let arity_indices, cstr_sort = Reductionops.splay_arity cenv sigma arity in
  (* Interpret the constructor types *)
  let interp_cstr (sigma, env, ncstrs, lifted_params) cname ctyp =
    let flags =
      Pretyping.{ all_no_fail_flags with
                  use_typeclasses = UseTCForConv;
                  solve_unification_constraints = false }
    in
    let env_par = EConstr.push_rel_context lifted_params env in
    let sigma, (ctyp, cimpl) = interp_type_evars_impls ~flags env_par sigma ~impls ctyp in
    let rty = Retyping.relevance_of_type env_par sigma ctyp in
    let annot = make_annot (Name cname) rty in
    let ctyppar = EConstr.it_mkProd_or_LetIn ctyp lifted_params in
    let decl = LocalAssum (annot, ctyppar) in
    let ctx, concl = Reductionops.splay_prod_assum env_par sigma ctyp in
    let concl_env = EConstr.push_rel_context ctx env_par in
    let sigma_with_model_evars, model =
      model_conclusion concl_env sigma ind_rel lifted_params
        (Context.Rel.length ctx) ncstrs arity_indices
    in
    (* unify the expected with the provided conclusion *)
    let sigma =
      try Evarconv.unify concl_env sigma_with_model_evars Reduction.CONV concl model
      with Evarconv.UnableToUnify (sigma,e) ->
        user_err (Himsg.explain_pretype_error concl_env sigma
                    (Pretype_errors.CannotUnify (concl, model, (Some e))))
    in
    (sigma, EConstr.push_rel decl env, succ ncstrs, lift_context 1 lifted_params),
    ((annot, ctyp), cimpl)
  in
  let (sigma, cenv, ncstrs, lifted_params), (ctyps, cimpls) =
    on_snd List.split @@
    List.fold_left2_map interp_cstr (sigma, cenv, ncstrs, lifted_params) cnames ctyps
  in
  (sigma, cenv, pred ind_rel, ncstrs, lifted_params), (cnames, ctyps, cimpls)

let sign_level env evd sign =
  fst (List.fold_right
    (fun d (lev,env) ->
      match d with
      | LocalDef _ -> lev, push_rel d env
      | LocalAssum _ ->
        let s = Retyping.get_sort_of env evd (EConstr.of_constr (RelDecl.get_type d)) in
        let u = univ_of_sort s in
          (Univ.sup u lev, push_rel d env))
    sign (Univ.Universe.sprop,env))

let sup_list min = List.fold_left Univ.sup min

let extract_level env evd min params tys =
  let env, sorts = List.fold_left_map (fun env ty ->
    let env_par = EConstr.push_rel_context params env in
    let ctx, concl = Reduction.dest_prod_assum env_par ty in
    let rty = Retyping.relevance_of_type env_par evd (EConstr.of_constr ty) in
    let fullty = EConstr.it_mkProd_or_LetIn (EConstr.of_constr ty) params in
    let decl = LocalAssum (make_annot Anonymous rty, fullty) in
    (EConstr.push_rel decl env, sign_level env_par evd (LocalAssum (make_annot Anonymous Sorts.Relevant, concl) :: ctx)))
    env tys
  in env, sup_list min sorts

let is_flexible_sort evd u =
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

(**********************************************************************)
(* Tools for template polymorphic inductive types                         *)

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
  | Some u -> Univ.univ_level_mem u v
  | None -> false

let solve_constraints_system levels level_bounds =
  let open Univ in
  let levels =
    Array.mapi (fun i o ->
      match o with
      | Some u ->
        (match Universe.level u with
        | Some u -> Some u
        | _ -> level_bounds.(i) <- Universe.sup level_bounds.(i) u; None)
      | None -> None)
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  let clos = Array.map (fun _ -> Int.Set.empty) levels in
  (* First compute the transitive closure of the levels dependencies *)
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
        clos.(i) <- Int.Set.add j clos.(i);
    done;
  done;
  let rec closure () =
    let continue = ref false in
      Array.iteri (fun i deps ->
        let deps' =
          Int.Set.fold (fun j acc -> Int.Set.union acc clos.(j)) deps deps
        in
          if Int.Set.equal deps deps' then ()
          else (clos.(i) <- deps'; continue := true))
        clos;
      if !continue then closure ()
      else ()
  in
  closure ();
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && Int.Set.mem j clos.(i) then
        (v.(i) <- Universe.sup v.(i) level_bounds.(j));
    done;
  done;
  v

let inductive_levels env env_ar evd params names relevances (arities : Constr.types list) inds =
  let env_par = EConstr.push_rel_context params env in
  let env_par_ar, destarities =
    List.fold_left3_map (fun env_par_ar na r ar ->
      let da = Reduction.dest_arity env_par_ar ar in
      let env_par_ar' = push_rel (LocalAssum (Context.make_annot (Name na) r, ar)) env_par_ar in
      env_par_ar', (ar, env_par_ar, da))
    env_par names relevances arities
  in
  let levels = List.map (fun (x,_,(ctx,a)) ->
    if Sorts.is_prop a || Sorts.is_sprop a then None
    else Some (univ_of_sort a)) destarities
  in
  let cstrs_levels, min_levels, sizes =
    CList.split3 @@ snd @@
      (List.fold_left2_map (fun env (_,tys) (arity,env_arity,(ctx,du)) ->
        let len = List.length tys in
        let minlev = Sorts.univ_of_sort du in
        let minlev =
          if len > 1 && not (is_impredicative_sort env du) then
            Univ.sup minlev Univ.type0_univ
          else minlev
        in
        let minlev =
          (* Indices contribute. *)
          if indices_matter env && List.length ctx > 0 then (
            let ilev = sign_level env_arity evd ctx in
              Univ.sup ilev minlev)
          else minlev
        in
        let env, clev = extract_level env evd minlev params tys in
          env, (clev, minlev, len))
        env_ar inds destarities)
  in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels)
  in
  let evd, arities =
    CList.fold_left3 (fun (evd, arities) cu (arity,_,(ctx,du)) len ->
      if is_impredicative_sort env du then
        (* Any product is allowed here. *)
        evd, (false, arity) :: arities
      else (* If in a predicative sort, or asked to infer the type,
              we take the max of:
              - indices (if in indices-matter mode)
              - constructors
              - Type(1) if there is more than 1 constructor
           *)
        (* Constructors contribute. *)
        let evd =
          if Sorts.is_set du then
            if not (Evd.check_leq evd cu Univ.type0_univ) then
              raise (InductiveError LargeNonPropInductiveNotInType)
            else evd
          else evd
        in
        let evd =
          if len >= 2 && Univ.is_type0m_univ cu then
           (* "Polymorphic" type constraint and more than one constructor,
               should not land in Prop. Add constraint only if it would
               land in Prop directly (no informative arguments as well). *)
            Evd.set_leq_sort env evd Sorts.set du
          else evd
        in
        let duu = Sorts.univ_of_sort du in
        let template_prop, evd =
          if not (Univ.is_small_univ duu) && Univ.Universe.equal cu duu then
            if is_flexible_sort evd duu && not (Evd.check_leq evd Univ.type0_univ duu) then
              true, Evd.set_eq_sort env evd Sorts.prop du
            else false, evd
          else false, Evd.set_eq_sort env evd (sort_of_univ cu) du
        in
          (evd, (template_prop, arity) :: arities))
    (evd,[]) (Array.to_list levels') destarities sizes
  in evd, List.rev arities

let check_named {CAst.loc;v=na} = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err ?loc  msg

let template_polymorphism_candidate ~ctor_levels uctx params concl =
  match uctx with
  | Entries.Monomorphic_entry uctx ->
    let concltemplate = Option.cata (fun s -> not (Sorts.is_small s)) false concl in
    if not concltemplate then false
    else
      let conclu = Option.cata Sorts.univ_of_sort Univ.type0m_univ concl in
      Option.has_some @@ IndTyping.template_polymorphic_univs ~ctor_levels uctx params conclu
  | Entries.Polymorphic_entry _ -> false

let check_param = function
| CLocalDef (na, _, _) -> check_named na
| CLocalAssum (nas, Default _, _) -> List.iter check_named nas
| CLocalAssum (nas, Generalized _, _) -> ()
| CLocalPattern {CAst.loc} ->
    Loc.raise ?loc (Stream.Error "pattern with quote not allowed here")

let restrict_inductive_universes sigma ctx_params arities constructors =
  let merge_universes_of_constr c =
    Univ.LSet.union (EConstr.universes_of_constr sigma (EConstr.of_constr c)) in
  let uvars = Univ.LSet.empty in
  let uvars = Context.Rel.(fold_outside (Declaration.fold_constr merge_universes_of_constr) ctx_params ~init:uvars) in
  let uvars = List.fold_right merge_universes_of_constr arities uvars in
  let uvars = List.fold_right (fun (_,ctypes) -> List.fold_right merge_universes_of_constr ctypes) constructors uvars in
  Evd.restrict_universe_context sigma uvars

let interp_mutual_inductive_constr ~sigma ~template ~udecl ~ctx_params ~indnames ~relevances
  ~arities ~arityconcl ~constructors ~env ~env_ar ~cumulative ~poly ~private_ind ~finite =
  (* Compute renewed arities *)
  let sigma = Evd.minimize_universes sigma in
  let nf = Evarutil.nf_evars_universes sigma in
  let constructors = List.map (on_snd (List.map nf)) constructors in
  let arities = List.map EConstr.(to_constr sigma) arities in
  let sigma = List.fold_left make_anonymous_conclusion_flexible sigma arityconcl in

  let sigma, arities = inductive_levels env env_ar sigma ctx_params indnames relevances arities constructors in
  let sigma = Evd.minimize_universes sigma in
  let nf = Evarutil.nf_evars_universes sigma in
  let arities = List.map (on_snd nf) arities in
  let constructors = List.map (on_snd (List.map nf)) constructors in
  let ctx_params = List.map Termops.(map_rel_decl (EConstr.to_constr sigma)) ctx_params in
  let arityconcl = List.map (Option.map (fun (_anon, s) -> EConstr.ESorts.kind sigma s)) arityconcl in
  let sigma = restrict_inductive_universes sigma ctx_params (List.map snd arities) constructors in
  let uctx = Evd.check_univ_decl ~poly sigma udecl in

  (* Build the inductive entries *)
  let entries = List.map4 (fun indname (templatearity, arity) concl (cnames,ctypes) ->
      { mind_entry_typename = indname;
        mind_entry_arity = arity;
        mind_entry_consnames = cnames;
        mind_entry_lc = ctypes
      })
      indnames arities arityconcl constructors
  in
  let template = List.map4 (fun indname (templatearity, _) concl (_, ctypes) ->
      let template_candidate () =
        templatearity ||
        let ctor_levels =
          let add_levels c levels = Univ.LSet.union levels (Vars.universes_of_constr c) in
          let param_levels =
            List.fold_left (fun levels d -> match d with
                | LocalAssum _ -> levels
                | LocalDef (_,b,t) -> add_levels b (add_levels t levels))
              Univ.LSet.empty ctx_params
          in
          List.fold_left (fun levels c -> add_levels c levels)
            param_levels ctypes
        in
        template_polymorphism_candidate ~ctor_levels uctx ctx_params concl
      in
      match template with
        | Some template ->
          if poly && template then user_err
              Pp.(strbrk "Template-polymorphism and universe polymorphism are not compatible.");
          template
        | None ->
          should_auto_template indname (template_candidate ())
      )
      indnames arities arityconcl constructors
  in
  let is_template = List.for_all (fun t -> t) template in
  (* Build the mutual inductive entry *)
  let mind_ent =
    { mind_entry_params = ctx_params;
      mind_entry_record = None;
      mind_entry_finite = finite;
      mind_entry_inds = entries;
      mind_entry_private = if private_ind then Some false else None;
      mind_entry_universes = uctx;
      mind_entry_template = is_template;
      mind_entry_cumulative = poly && cumulative;
    }
  in
  mind_ent, Evd.universe_binders sigma

let interp_params env udecl uparamsl paramsl =
  let sigma, udecl = interp_univ_decl_opt env udecl in
  let sigma, (uimpls, ((env_uparams, ctx_uparams), useruimpls)) =
    interp_context_evars ~program_mode:false env sigma uparamsl in
  let sigma, (impls, ((env_params, ctx_params), userimpls)) =
    interp_context_evars ~program_mode:false ~impl_env:uimpls env_uparams sigma paramsl
  in
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter is_local_assum ctx_params in
  sigma, env_params, (ctx_params, env_uparams, ctx_uparams,
  List.map (RelDecl.get_name %> Name.get_id) assums, userimpls, useruimpls, impls, udecl)

(* When a hole remains for a param, pretend the param is uniform and
   do the unification.
   [env_ar_cstrs_par] is [uparams; inds; constructors; params]
 *)
let maybe_unify_params_in env_ar_cstrs_par sigma ~ninds ~nparams ~ncstrs c =
  let is_ind sigma k c = match EConstr.kind sigma c with
    | Constr.Rel n ->
      (* env is [uparams; inds; ncstrs; params; k other things] *)
      n > k + ncstrs + nparams && n <= k + ncstrs + nparams + ninds
    | _ -> false
  in
  let rec aux (env,k as envk) sigma c = match EConstr.kind sigma c with
    | Constr.App (h,args) when is_ind sigma k h ->
      Array.fold_left_i (fun i sigma arg ->
          if i >= nparams || not (EConstr.isEvar sigma arg) then sigma
          else Evarconv.unify_delay env sigma arg (EConstr.mkRel (k+nparams-i)))
        sigma args
    | _ -> Termops.fold_constr_with_full_binders
             sigma
             (fun d (env,k) -> EConstr.push_rel d env, k+1)
             aux envk sigma c
  in
  aux (env_ar_cstrs_par,0) sigma c

let interp_arities sigma env_params ctx_params indl = 
  let nparams = Context.Rel.length ctx_params in
  let interp_arity (sigma, (env, subst, i, decls)) ind =
    let arity = intern_ind_arity env sigma ind in
    let sigma, (t, relevance, poly, impls) = pretype_ind_arity env sigma arity in
    (* let signlev =
      let ctx, s = EConstr.dest_arity env t in
      if Indtypes.is_indices_matter () && List.length ctx > 0 then
	        Some (sign_level env !evdref ctx)
      else None
    in *)
    let t = EConstr.Vars.substl subst t in
    let full = EConstr.it_mkProd_or_LetIn t ctx_params in
    let decl = LocalAssum (make_annot (Name ind.ind_name) relevance, full) in
    (sigma, (EConstr.push_rel decl env, EConstr.mkRel (nparams + 1) :: List.map (EConstr.Vars.lift 1) subst,
     succ i, full :: decls)), (t, relevance, poly, impls)
  in
  let (sigma, (aritiesenv, _, _, fullarities)), arities =
    List.fold_left_map interp_arity (sigma, (env_params, [], 0, [])) indl in
  let fullarities = List.rev fullarities in
  sigma, fullarities, arities

let interp_mutual_inductive_gen env0 ~template udecl (uparamsl,paramsl,indl) notations ~cumulative ~poly ~private_ind finite =
  check_all_names_different indl;
  List.iter check_param paramsl;
  if not (List.is_empty uparamsl) && not (List.is_empty notations)
  then user_err (str "Inductives with uniform parameters may not have attached notations.");

  let indnames = List.map (fun ind -> ind.ind_name) indl in

  (* In case of template polymorphism, we need to compute more constraints *)
  let env0 = if poly then env0 else Environ.set_universes_lbound env0 UGraph.Bound.Prop in

  let sigma, env_params, (ctx_params, env_uparams, ctx_uparams, params, userimpls, useruimpls, impls, udecl) =
    interp_params env0 udecl uparamsl paramsl
  in

  (* Interpret the arities *)
  let sigma, fullarities, arities = interp_arities sigma env_params ctx_params indl in
  let arities, relevances, arityconcl, indimpls = List.split4 arities in

  let ninds = List.length indl in

  (* We lift over the arities to account for dependencies between uniform parameters and regular ones *)
  let ctx_params_lifted, fullarities = CList.fold_left_map
      (fun ctx_params c -> lift_context 1 ctx_params, EConstr.it_mkProd_or_LetIn c ctx_params)
      ctx_params
      arities
  in

  let env_ar = push_types env_uparams indnames relevances fullarities in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun impls -> userimpls @ impls) indimpls in
  let impls = compute_internalization_env env_uparams sigma ~impls Inductive indnames fullarities indimpls in
  let ntn_impls = compute_internalization_env env_uparams sigma Inductive indnames fullarities indimpls in

  let (sigma, _env_ar_cstrs, _ind_rel, _nconstrs, _lifted_params), constructors =
    Metasyntax.with_syntax_protection (fun () ->
        (* Temporary declaration of notations and scopes *)
        List.iter (Metasyntax.set_notation_for_interpretation env_params ntn_impls) notations;
        (* Interpret the constructor types *)
        List.fold_left2_map (fun acc -> interp_cstrs acc impls)
          (sigma, env_ar, ninds, 0, ctx_params_lifted) indl arities)
      ()
  in
  let nparams = Context.Rel.length ctx_params in
  let _, _, sigma, _ =
    List.fold_left (fun (ncstrs, env, sigma, lifted_params) (_,ctyps,_) ->
      List.fold_left (fun (ncstrs, env, sigma, lifted_params) (ann, ctyp) ->
        let lifted_params = lift_context 1 lifted_params in
        (* We must redo the lifts for each constructor *)
        let env_pars = EConstr.push_rel_context lifted_params env in
        let sigma = maybe_unify_params_in env_pars sigma ~ninds ~nparams ~ncstrs ctyp in
        (ncstrs + 1, EConstr.push_rel (LocalAssum (ann, ctyp)) env, sigma, lifted_params))
      (ncstrs, env, sigma, lifted_params) ctyps)
    (0, env_ar, sigma, ctx_params_lifted) constructors
  in

  (* generalize over the uniform parameters *)
  let nuparams = Context.Rel.length ctx_uparams in
  let uargs = Context.Rel.to_extended_vect EConstr.mkRel 0 ctx_uparams in
  let uparam_subst ncstrs =
    List.init (List.length indl + ncstrs) EConstr.(fun i -> mkApp (mkRel (i + 1 + nuparams), uargs))
    @ List.init nuparams EConstr.(fun i -> mkRel (i + 1)) in
  let generalize_constructor ncstrs (ann, c) =
    let c' = EConstr.Unsafe.to_constr (EConstr.Vars.substnl (uparam_subst ncstrs) nparams c) in
    succ ncstrs, c'
  in
  let cimpls = List.map pi3 constructors in
  let _ncstrs, constructors = List.fold_left_map (fun ncstrs (cnames,ctypes,cimpls) ->
      let ncstrs, ctypes' = List.fold_left_map generalize_constructor ncstrs ctypes in
        ncstrs, (cnames, ctypes'))
      0 constructors
  in
  let ctx_params = ctx_params @ ctx_uparams in
  let userimpls = useruimpls @ userimpls in
  let indimpls = List.map (fun iimpl -> useruimpls @ iimpl) indimpls in
  let fullarities = List.map (fun c -> EConstr.it_mkProd_or_LetIn c ctx_uparams) fullarities in
  let env_ar = push_types env0 indnames relevances fullarities in
  (* Now each constructor is typed in [fullarities; cstrs; ctx_params] *)

  (* Try further to solve evars, and instantiate them *)

  let sigma = solve_remaining_evars all_and_fail_flags env_params sigma in
  let impls =
    List.map2 (fun indimpls cimpls ->
        indimpls, List.map (fun impls ->
            userimpls @ impls) cimpls)
      indimpls cimpls
  in
  let mie, pl = interp_mutual_inductive_constr ~template ~sigma ~ctx_params ~udecl
    ~indnames ~relevances ~arities
    ~arityconcl ~constructors ~env:env0 ~env_ar ~poly ~finite ~cumulative ~private_ind
    in
  (mie, pl, impls)


(* Very syntactical equality *)
let eq_local_binders bl1 bl2 =
  List.equal local_binder_eq bl1 bl2

let eq_params (up1,p1) (up2,p2) =
  eq_local_binders up1 up2 && Option.equal eq_local_binders p1 p2

let extract_coercions indl =
  let mkqid (_,({CAst.v=id},_)) = qualid_of_ident id in
  let extract lc = List.filter (fun (iscoe,_) -> iscoe) lc in
  List.map mkqid (List.flatten(List.map (fun (_,_,_,lc) -> extract lc) indl))

let extract_params indl =
  let paramsl = List.map (fun (_,params,_,_) -> params) indl in
  match paramsl with
  | [] -> anomaly (Pp.str "empty list of inductive types.")
  | params::paramsl ->
      if not (List.for_all (eq_params params) paramsl) then user_err Pp.(str
        "Parameters should be syntactically the same for each inductive type.");
      params

let extract_inductive indl =
  List.map (fun ({CAst.v=indname},_,ar,lc) -> {
    ind_name = indname;
    ind_arity = Option.cata (fun x -> x) (CAst.make @@ CSort (Glob_term.UAnonymous {rigid=true})) ar;
    ind_lc = List.map (fun (_,({CAst.v=id},t)) -> (id,t)) lc
  }) indl

let extract_mutual_inductive_declaration_components indl =
  let indl,ntnl = List.split indl in
  let params = extract_params indl in
  let coes = extract_coercions indl in
  let indl = extract_inductive indl in
  (params,indl), coes, List.flatten ntnl

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

let do_mutual_inductive ~template udecl indl ~cumulative ~poly ~private_ind ~uniform finite =
  let (params,indl),coes,ntns = extract_mutual_inductive_declaration_components indl in
  (* Interpret the types *)
  let indl = match params with
    | uparams, Some params -> (uparams, params, indl)
    | params, None -> match uniform with
      | UniformParameters -> (params, [], indl)
      | NonUniformParameters -> ([], params, indl)
  in
  let mie,pl,impls = interp_mutual_inductive_gen (Global.env()) ~template udecl indl ntns ~cumulative ~poly ~private_ind finite in
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (DeclareInd.declare_mutual_inductive_with_eliminations mie pl impls);
  (* Declare the possible notations of inductive types *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env ())) ntns;
  (* Declare the coercions *)
  List.iter (fun qid -> ComCoercion.try_add_new_coercion (Nametab.locate qid) ~local:false ~poly) coes

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

(*

  HH notes in PR #679:

  The Show Match could also be made more robust, for instance in the
  presence of let in the branch of a constructor. A
  decompose_prod_assum would probably suffice for that, but then, it
  is a Context.Rel.Declaration.t which needs to be matched and not
  just a pair (name,type).

  Otherwise, this is OK. After all, the API on inductive types is not
  so canonical in general, and in this simple case, working at the
  low-level of mind_nf_lc seems reasonable (compared to working at the
  higher-level of Inductiveops).

*)

let make_cases ind =
  let open Declarations in
  let mib, mip = Global.lookup_inductive ind in
  Util.Array.fold_right_i
    (fun i (ctx, _) l ->
       let al = Util.List.skipn (List.length mib.mind_params_ctxt) (List.rev ctx) in
       let rec rename avoid = function
         | [] -> []
         | RelDecl.LocalDef _ :: l -> "_" :: rename avoid l
         | RelDecl.LocalAssum (n, _)::l ->
           let n' = Namegen.next_name_away_with_default (Id.to_string Namegen.default_dependent_ident) n.Context.binder_name avoid in
           Id.to_string n' :: rename (Id.Set.add n' avoid) l in
       let al' = rename Id.Set.empty al in
       let consref = GlobRef.ConstructRef (ith_constructor_of_inductive ind (i + 1)) in
       (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty consref) :: al') :: l)
    mip.mind_nf_lc []

let declare_mutual_inductive_with_eliminations = DeclareInd.declare_mutual_inductive_with_eliminations
