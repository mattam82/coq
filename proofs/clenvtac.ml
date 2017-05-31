(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Termops
open Evd
open Refiner
open Logic
open Reduction
open Tacmach
open Clenv
open Proofview.Notations

(* This function put casts around metavariables whose type could not be
 * infered by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv =
  let rec crec u =
    match kind_of_term u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_,_) when isMeta c -> u
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _  -> map_constr crec u

  and crec_hd u =
    match kind_of_term (strip_outer_cast u) with
      | Meta mv ->
	  (try
            let b = Typing.meta_type clenv.evd mv in
	    assert (not (occur_meta b));
	    if occur_meta b then u
            else mkCast (mkMeta mv, DEFAULTcast, b)
	  with Not_found -> u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _ -> u
  in
  crec

let clenv_value_cast_meta clenv =
    clenv_cast_meta clenv (clenv_value clenv)

let clenv_pose_dependent_evars with_evars clenv =
  let dep_mvs = clenv_dependent clenv in
  if not (List.is_empty dep_mvs) && not with_evars then
    raise
      (RefinerError (UnresolvedBindings (List.map (meta_name clenv.evd) dep_mvs)));
  clenv_pose_metas_as_evars clenv dep_mvs

let clenv_refine with_evars ?(with_classes=true) clenv =
  (** ppedrot: a Goal.enter here breaks things, because the tactic below may
      solve goals by side effects, while the compatibility layer keeps those
      useless goals. That deserves a FIXME. *)
  Proofview.V82.tactic begin fun gl ->
  let clenv = clenv_pose_dependent_evars with_evars clenv in
  let evd' =
    if with_classes then
      let evd' = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        ~fail:(not with_evars) clenv.env clenv.evd
      in Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals evd'
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  tclTHEN
    (tclEVARS (Evd.clear_metas evd'))
    (refine_no_check (clenv_cast_meta clenv (clenv_value clenv))) gl
  end

let clenv_unify_concl flags clenv =
  let open Ftactic.Notations in
  Ftactic.enter { enter = begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
  try let sigma, clenv = clenv_unify_concl env sigma flags concl clenv in
      Ftactic.return (sigma, clenv)
  with Evarconv.UnableToUnify (evd, reason) ->
    let ex = Pretype_errors.(PretypeError (env, evd,
        CannotUnify (concl, clenv_concl clenv, Some reason))) in
    Ftactic.lift (Proofview.tclZERO ex) end }

let debug_print_goal =
  Proofview.Goal.enter { enter = begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let concl = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
  (Feedback.msg_debug Pp.(str"After clenv_refine_gen: " ++
                            print_constr_env env concl);
   Proofview.tclUNIT ())
  end }

let holes_goals holes =
  List.map (fun h -> fst (destEvar h.hole_evar)) holes

let clenv_check_dep_holes with_evars sigma ?origsigma clenv =
  let holes = clenv_dep_holes clenv in
  if not with_evars then
    let holes' =
      match origsigma with
      | None -> holes
      | Some origsigma ->
         let origevars = Evar.Map.domain (Evd.undefined_map origsigma) in
         let filter h = not (Evarutil.reachable_from_evars sigma origevars (fst (destEvar h.hole_evar))) in
         List.filter filter holes
    in
     if not (List.is_empty holes') then
       Proofview.tclZERO
         (Logic.RefinerError (Logic.UnresolvedBindings
                                (List.map (fun h -> h.hole_name) holes')))
     else Proofview.tclUNIT (holes_goals holes)
  else Proofview.tclUNIT (holes_goals holes)

let rec rename_evar_concl ctxt t =
  match ctxt, kind_of_term t with
  | decl :: decls, Prod (na, b, t) ->
     mkProd (Context.Rel.Declaration.get_name decl, b, rename_evar_concl decls t)
  | decl :: decls, LetIn (na, b, t', t) ->
     mkLetIn (Context.Rel.Declaration.get_name decl, b, t', rename_evar_concl decls t)
  | [], _ -> t
  | _ :: _, _ -> raise (Invalid_argument "rename_evar_concl")

let rename_term env sigma t =
  let evd = ref sigma in
  let rename_branches ci tys brs =
    let rename i ty =
      let ndecls = ci.ci_cstr_ndecls.(i) in
      let ctxt, tyctx = decompose_prod_n_assum ndecls ty in
      let ctxt = List.rev ctxt in
      let hd, args = decompose_app (Evarutil.whd_evar !evd brs.(i)) in
      match kind_of_term hd with
      | Evar (ev, args) ->
         let evi = Evd.find_undefined !evd ev in
         let concl' = rename_evar_concl ctxt
                                        (Evarutil.nf_evar !evd (evar_concl evi)) in
         evd := Evd.add !evd ev { evi with evar_concl = concl' }
      | _ -> ()
    in Array.iteri rename tys
  in
  let rec aux env c =
    match kind_of_term c with
    | Case (ci,p,c,brs) ->
       let ct = Retyping.get_type_of env sigma c in
       let indspec =
         try Tacred.find_hnf_rectype env sigma ct
         with Not_found -> CErrors.anomaly (Pp.str "mk_casegoals") in
       let (lbrty,_) = Inductiveops.type_case_branches_with_names env indspec p c in
       let () = rename_branches ci lbrty brs in
       mkCase (ci,p,aux env c,Array.map (aux env) brs)
    | _ -> map_constr_with_full_binders Environ.push_rel aux env c
  in
  let t' = aux env t in
  !evd, t'

let debug_print_shelf s =
  let open Proofview in
  let open Proofview.Notations in
  let print_goal env sigma gl =
    let evi = Evd.find sigma gl in
    let concl = evi.evar_concl in
    (Feedback.msg_debug Pp.(int (Evar.repr gl) ++ str" : " ++ print_constr_env env concl))
  in
  Proofview.shelf >>= fun shelf ->
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
    (Feedback.msg_debug (Pp.str s);
     Feedback.msg_debug (Pp.str "shelf:");
     List.iter (print_goal env sigma) shelf;
     Feedback.msg_debug (Pp.str "future goals:");
     List.iter (print_goal env sigma) (Evd.future_goals sigma);
     tclUNIT ())

let clenv_refine_gen ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?origsigma
                     flags (sigma, clenv) =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter { enter = begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma =
    try Evarconv.consider_remaining_unif_problems ~flags env sigma with _ -> sigma in
  let sigma =
    if with_classes then
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        (* Don't split as this can result in typeclasses not failing due
           to initial holes not being marked as "mandatory". *)
        ~split:false ~fail:(not with_evars) env sigma
      in Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals sigma
    else sigma
  in
  let run sigma =
    let declare_goal sigma h =
      let ev, _ = destEvar h.hole_evar in
      declare_future_goal ev sigma
    in
    let sigma = List.fold_left declare_goal (Sigma.to_evar_map sigma)
                               (clenv_holes clenv) in
    let v = nf_betaiota env (clenv_val clenv) in
    (** This renaming hack should really stop at 8.6 *)
    let sigma, v =
      if Flags.version_less_or_equal Flags.Current then
        rename_term env sigma v
      else sigma, v
    in
    Sigma.here v (Sigma.Unsafe.of_evar_map sigma)
  in
  let reduce_goal gl =
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let glev = Proofview.Goal.goal gl in
    let sigma = Sigma.to_evar_map sigma in
    (* For compatibility: beta iota reduction *)
    let concl = Reductionops.clos_norm_flags CClosure.betaiota env sigma concl in
    let evi = Evd.find sigma glev in
    let sigma = Evd.add sigma glev { evi with evar_concl = concl } in
    Proofview.Unsafe.tclEVARS sigma
  in
  Proofview.Unsafe.tclEVARS sigma <*>
    clenv_check_dep_holes with_evars sigma ?origsigma clenv >>= (fun deps ->
  (Refine.refine ~unsafe:true { Sigma.run = run }) <*>
  (if shelve_subgoals then shelve_goals deps else tclUNIT ()) <*>
    Proofview.Goal.nf_enter { enter = reduce_goal })
  end }

open Unification

let dft = default_unify_flags

let clenv_refine_no_check
      ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
      ?(flags=dft ()) ?origsigma clenv =
  let flags = flags_of flags in
  Proofview.tclEVARMAP >>= fun sigma ->
  clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                   flags (sigma, clenv)

let clenv_refine2 ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
                  ?(flags=dft ()) clenv =
  let flags = flags_of flags in
  let tac = clenv_unify_concl flags clenv in
  Ftactic.run tac
              (clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals
                                flags)

(** The dependent holes turned into subgoals are 
    
    - evars of the clause which are dependent in other hypotheses of the clause,
      whether or not they appear in the instantiated conclusion.
 *)
  
let clenv_refine_bindings
    ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
    ?(flags=dft ()) ~hyps_only ~delay_bindings b ?origsigma clenv =
  let open Proofview in
  let flags = flags_of flags in
  Proofview.Goal.enter { enter = fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Sigma.to_evar_map (Proofview.Goal.sigma gl) in
    let sigma, clenv, bindings =
      if delay_bindings then
        sigma, clenv, Some (None, b)
      else
        try let sigma, clenv = Clenv.solve_evar_clause env sigma ~hyps_only clenv b in
            sigma, clenv, None
        with e -> sigma, clenv, Some (Some e, b)
    in
    let tac = clenv_unify_concl flags clenv in
    (Unsafe.tclEVARS sigma) <*>
    (Ftactic.run tac
      (fun (sigma, clenv) ->
        let sigma, clenv =
          match bindings with
          | Some (exn, b) ->
             (* Hack to make [exists 0] on [Σ x : nat, True] work, we
                use implicit bindings for a hole that's not dependent
                after unification, but reuse the typing information. *)
             Clenv.solve_evar_clause env sigma ~hyps_only:false clenv b
          | None -> sigma, clenv_recompute_deps sigma ~hyps_only:false clenv
        in
        clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                         flags (sigma, clenv))) }

let res_pf ?(with_evars=false) ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter { enter = begin fun gl ->
    let clenv gl = clenv_unique_resolver ~flags clenv gl in
    clenv_refine with_evars ~with_classes (Tacmach.New.of_old clenv (Proofview.Goal.assume gl))
  end }

let clenv_solve_clause_constraints ?(flags=dft ()) ~with_ho clenv =
  let open Proofview in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma -> 
    try
      let flags = flags_of flags in
      let sigma' =
        Evarconv.consider_remaining_unif_problems env ~flags ~with_ho sigma
      in Unsafe.tclEVARS sigma' <*> tclUNIT (clenv_advance sigma' clenv)
    with e -> tclZERO e
                       
(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

let fail_quick_core_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true; (* ? *)
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = false;
  modulo_eta = true;
}

let fail_quick_unif_flags = {
  core_unify_flags = fail_quick_core_unif_flags;
  merge_unify_flags = fail_quick_core_unif_flags;
  subterm_unify_flags = fail_quick_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unify ?(flags=fail_quick_unif_flags) ?(with_ho=true) m =
  Proofview.Goal.enter { enter = begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let n = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
    let sigma = Tacmach.New.project gl in
    try
      let sigma = Evd.add_conv_pb (CONV,env,m,n) sigma in
      let flags = Clenv.flags_of flags in
      let sigma = Evarconv.consider_remaining_unif_problems ~flags ~with_ho env sigma in
	Proofview.Unsafe.tclEVARSADVANCE sigma
    with e when CErrors.noncritical e -> Proofview.tclZERO e
  end }
