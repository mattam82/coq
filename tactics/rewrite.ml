(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Errors
open Util
open Names
open Nameops
open Namegen
open Term
open Vars
open Termops
open Reduction
open Tacticals
open Tacmach
open Tactics
open Patternops
open Clenv
open Glob_term
open Typeclasses
open Typeclasses_errors
open Classes
open Constrexpr
open Libnames
open Globnames
open Evd
open Misctypes
open Locus
open Locusops
open Decl_kinds
open Tacinterp
open Elimschemes
open Goal
open Environ
open Tacinterp
open Termops
open Genarg
open Extraargs
open Pcoq.Constr
open Entries
open Libnames
open Evarutil

(** Typeclass-based generalized rewriting. *)

(** Constants used by the tactic. *)

let classes_dirpath =
  DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let try_find_global_reference dir s =
  let sp = Libnames.make_path (make_dir ("Coq"::dir)) (Id.of_string s) in
    Nametab.global_of_path sp

let find_reference dir s =
  let gr = lazy (try_find_global_reference dir s) in
    fun () -> Lazy.force gr

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

let find_global dir s =
  let gr = lazy (try_find_global_reference dir s) in
    fun (evd,cstrs) -> 
      let evd, c = Evarutil.new_global evd (Lazy.force gr) in
	(evd, cstrs), c

(** Utility for dealing with polymorphic applications *)

let app_poly evars f args =
  let evars, fc = f evars in
    evars, mkApp (fc, args)

let e_app_poly evars f args =
  let evars', c = app_poly !evars f args in
    evars := evars';
    c

(** Global constants. *)

let gen_reference dir s = Coqlib.gen_reference "rewrite" dir s
let coq_eq_ref = find_reference ["Init"; "Logic"] "eq"
let coq_eq = find_global ["Init"; "Logic"] "eq"
let coq_f_equal = find_global ["Init"; "Logic"] "f_equal"
let coq_all = find_global ["Init"; "Logic"] "all"
let impl = find_global ["Program"; "Basics"] "impl"
let arrow = find_global ["Program"; "Basics"] "arrow"
let coq_inverse = find_global ["Program"; "Basics"] "flip"

(* let coq_inverse = lazy (gen_constant ["Program"; "Basics"] "flip") *)

(* let inverse car rel = mkApp (Lazy.force coq_inverse, [| car ; car; mkProp; rel |]) *)

(* let forall_relation = lazy (gen_constant ["Classes"; "Morphisms"] "forall_relation") *)
(* let pointwise_relation = lazy (gen_constant ["Classes"; "Morphisms"] "pointwise_relation") *)
(* let respectful = lazy (gen_constant ["Classes"; "Morphisms"] "respectful") *)
(* let default_relation = lazy (gen_constant ["Classes"; "SetoidTactics"] "DefaultRelation") *)
(* let subrelation = lazy (gen_constant ["Classes"; "RelationClasses"] "subrelation") *)
(* let do_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "do_subrelation") *)
(* let apply_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "apply_subrelation") *)
(* let coq_relation = lazy (gen_constant ["Relations";"Relation_Definitions"] "relation") *)
(* let mk_relation a = mkApp (Lazy.force coq_relation, [| a |]) *)

(* let proper_type = lazy (Universes.constr_of_global (Lazy.force proper_class).cl_impl) *)
(* let proper_proxy_type = lazy (Universes.constr_of_global (Lazy.force proper_proxy_class).cl_impl) *)



(** Bookkeeping which evars are constraints so that we can 
    remove them at the end of the tactic. *)

let goalevars evars = fst evars
let cstrevars evars = snd evars

let new_cstr_evar (evd,cstrs) env t =
  let evd', t = Evarutil.new_evar evd env t in
    (evd', Evar.Set.add (fst (destEvar t)) cstrs), t

let e_new_cstr_evar evars env t =
  let evd', t = new_cstr_evar !evars env t in evars := evd'; t

let new_goal_evar (evd,cstrs) env t =
  let evd', t = Evarutil.new_evar evd env t in
    (evd', cstrs), t

let e_new_goal_evar evars env t =
  let evd', t = new_goal_evar !evars env t in evars := evd'; t

(** Building or looking up instances. *)

let extends_undefined evars evars' =
  let f ev evi found = found || not (Evd.mem evars ev)
  in fold_undefined f evars' false

let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let evars, goal = app_poly evars proof_type [| carrier ; relation |] in
    let evars', c = Typeclasses.resolve_one_typeclass env (goalevars evars) goal in
      if extends_undefined (goalevars evars) evars' then raise Not_found
      else app_poly (evars',cstrevars evars) proof_method [| carrier; relation; c |]
  with e when Logic.catchable_exception e -> raise Not_found
 
(** Utility functions *)

module GlobalBindings (M : sig
  val relation_classes : string list
  val morphisms : string list
  val relation : string list * string
end) = struct
  open M
  let relation : evars -> evars * constr = find_global (fst relation) (snd relation)

  let reflexive_type = find_global relation_classes "Reflexive"
  let reflexive_proof = find_global relation_classes "reflexivity"
    
  let symmetric_type = find_global relation_classes "Symmetric"
  let symmetric_proof = find_global relation_classes "symmetry"

  let transitive_type = find_global relation_classes "Transitive"
  let transitive_proof = find_global relation_classes "transitivity"

  let forall_relation = find_global morphisms "forall_relation"
  let pointwise_relation = find_global morphisms "pointwise_relation"

  let forall_relation_ref = find_reference morphisms "forall_relation"
  let pointwise_relation_ref = find_reference morphisms "pointwise_relation"

  let respectful = find_global morphisms "respectful"
  let respectful_ref = find_reference morphisms "respectful"

  let default_relation = find_global ["Classes"; "SetoidTactics"] "DefaultRelation"

  let coq_forall = find_global morphisms "forall_def"

  let subrelation = find_global relation_classes "subrelation"
  let do_subrelation = find_global morphisms "do_subrelation"
  let apply_subrelation = find_global morphisms "apply_subrelation"

  let rewrite_relation_class = find_global relation_classes "RewriteRelation"

  let proper_class = lazy (class_info (try_find_global_reference morphisms "Proper"))
  let proper_proxy_class = lazy (class_info (try_find_global_reference morphisms "ProperProxy"))
    
  let proper_proj = lazy (mkConst (Option.get (pi3 (List.hd (Lazy.force proper_class).cl_projs))))
    
  let proper_type = 
    let l = lazy (Lazy.force proper_class).cl_impl in
      fun (evd,cstrs) -> 
	let evd, c = Evarutil.new_global evd (Lazy.force l) in
	  (evd, cstrs), c
	
  let proper_proxy_type = 
    let l = lazy (Lazy.force proper_proxy_class).cl_impl in
      fun (evd,cstrs) -> 
	let evd, c = Evarutil.new_global evd (Lazy.force l) in
	  (evd, cstrs), c

  let proper_proof env evars carrier relation x =
    let evars, goal = app_poly evars proper_proxy_type [| carrier ; relation; x |] in
      new_cstr_evar evars env goal

  let get_reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
  let get_symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
  let get_transitive_proof env = find_class_proof transitive_type transitive_proof env

  let mk_relation evd a = 
    app_poly evd relation [| a |]

  (** Build an infered signature from constraints on the arguments and expected output
      relation *)
    
  let build_signature evars env m (cstrs : (types * types option) option list)
      (finalcstr : (types * types option) option) =
    let mk_relty evars newenv ty obj =
      match obj with
      | None | Some (_, None) ->
	let evars, relty = mk_relation evars ty in
	  if closed0 ty then 
	    let env' = Environ.reset_with_named_context (Environ.named_context_val env) env in
	      new_cstr_evar evars env' relty
	  else new_cstr_evar evars newenv relty
      | Some (x, Some rel) -> evars, rel
    in
    let rec aux env evars ty l =
      let t = Reductionops.whd_betadeltaiota env (goalevars evars) ty in
	match kind_of_term t, l with
	| Prod (na, ty, b), obj :: cstrs ->
	  if noccurn 1 b (* non-dependent product *) then
	    let ty = Reductionops.nf_betaiota (goalevars evars) ty in
	    let (evars, b', arg, cstrs) = aux env evars (subst1 mkProp b) cstrs in
	    let evars, relty = mk_relty evars env ty obj in
	    let evars, newarg = app_poly evars respectful [| ty ; b' ; relty ; arg |] in
	      evars, mkProd(na, ty, b), newarg, (ty, Some relty) :: cstrs
	  else
	    let (evars, b, arg, cstrs) = 
	      aux (Environ.push_rel (na, None, ty) env) evars b cstrs 
	    in
	    let ty = Reductionops.nf_betaiota (goalevars evars) ty in
	    let pred = mkLambda (na, ty, b) in
	    let liftarg = mkLambda (na, ty, arg) in
	    let evars, arg' = app_poly evars forall_relation [| ty ; pred ; liftarg |] in
	      if Option.is_empty obj then evars, mkProd(na, ty, b), arg', (ty, None) :: cstrs
	      else error "build_signature: no constraint can apply on a dependent argument"
	| _, obj :: _ -> anomaly ~label:"build_signature" (Pp.str "not enough products")
	| _, [] ->
	  (match finalcstr with
	  | None | Some (_, None) ->
	    let t = Reductionops.nf_betaiota (fst evars) ty in
	    let evars, rel = mk_relty evars env t None in
	      evars, t, rel, [t, Some rel]
	  | Some (t, Some rel) -> evars, t, rel, [t, Some rel])
    in aux env evars m cstrs

  (** Folding/unfolding of the tactic constants. *)

  let unfold_impl t =
    match kind_of_term t with
    | App (arrow, [| a; b |])(*  when eq_constr arrow (Lazy.force impl) *) ->
      mkProd (Anonymous, a, lift 1 b)
    | _ -> assert false

  let unfold_all t =
    match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match kind_of_term b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> assert false)
    | _ -> assert false

  let unfold_forall t =
    match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match kind_of_term b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> assert false)
    | _ -> assert false

  let arrow_morphism evd ta tb a b =
    let ap = is_Prop ta and bp = is_Prop tb in
      if ap && bp then app_poly evd impl [| a; b |], unfold_impl
      else if ap then (* Domain in Prop, CoDomain in Type *)
	(evd, mkProd (Anonymous, a, b)), (fun x -> x)
      else if bp then (* Dummy forall *)
	(app_poly evd coq_all [| a; mkLambda (Anonymous, a, b) |]), unfold_forall
      else (* None in Prop, use arrow *)
	(app_poly evd arrow [| a; b |]), unfold_impl

  let rec decomp_pointwise n c =
    if Int.equal n 0 then c
    else
      match kind_of_term c with
      | App (f, [| a; b; relb |]) when Globnames.is_global (pointwise_relation_ref ()) f ->
	decomp_pointwise (pred n) relb
      | App (f, [| a; b; arelb |]) when Globnames.is_global (forall_relation_ref ()) f ->
	decomp_pointwise (pred n) (Reductionops.beta_applist (arelb, [mkRel 1]))
      | _ -> invalid_arg "decomp_pointwise"

  let rec apply_pointwise rel = function
    | arg :: args ->
      (match kind_of_term rel with
      | App (f, [| a; b; relb |]) when Globnames.is_global (pointwise_relation_ref ()) f ->
	apply_pointwise relb args
      | App (f, [| a; b; arelb |]) when Globnames.is_global (forall_relation_ref ()) f ->
	apply_pointwise (Reductionops.beta_applist (arelb, [arg])) args
      | _ -> invalid_arg "apply_pointwise")
    | [] -> rel

  let pointwise_or_dep_relation evd n t car rel =
    if noccurn 1 car && noccurn 1 rel then
      app_poly evd pointwise_relation [| t; lift (-1) car; lift (-1) rel |]
    else
      app_poly evd forall_relation
	[| t; mkLambda (n, t, car); mkLambda (n, t, rel) |]

  let lift_cstr env evars (args : constr list) c ty cstr =
    let start evars env car =
      match cstr with
      | None | Some (_, None) -> 
	let evars, rel = mk_relation evars car in
	  new_cstr_evar evars env rel
      | Some (ty, Some rel) -> evars, rel
    in
    let rec aux evars env prod n = 
      if Int.equal n 0 then start evars env prod
      else
	match kind_of_term (Reduction.whd_betadeltaiota env prod) with
	| Prod (na, ty, b) ->
	  if noccurn 1 b then
	    let b' = lift (-1) b in
	    let evars, rb = aux evars env b' (pred n) in
	      app_poly evars pointwise_relation [| ty; b'; rb |]
	  else
	    let evars, rb = aux evars (Environ.push_rel (na, None, ty) env) b (pred n) in
	      app_poly evars forall_relation
		[| ty; mkLambda (na, ty, b); mkLambda (na, ty, rb) |]
	| _ -> raise Not_found
    in 
    let rec find env c ty = function
      | [] -> None
      | arg :: args ->
	try let evars, found = aux evars env ty (succ (List.length args)) in
	      Some (evars, found, c, ty, arg :: args)
	with Not_found ->
	  find env (mkApp (c, [| arg |])) (prod_applist ty [arg]) args
    in find env c ty args

  let unlift_cstr env sigma = function
    | None -> None
    | Some codom -> Some (decomp_pointwise 1 codom)

end

(* let my_type_of env evars c = Typing.e_type_of env evars c *)
(* let mytypeofkey = Profile.declare_profile "my_type_of";; *)
(* let my_type_of = Profile.profile3 mytypeofkey my_type_of *)


let type_app_poly env evd f args =
  let evars, c = app_poly evd f args in
  let evd', t = Typing.e_type_of env (goalevars evars) c in
    (evd', cstrevars evars), c

module PropGlobal = struct
  module Consts =
  struct 
    let relation_classes = ["Classes"; "RelationClasses"]
    let morphisms = ["Classes"; "Morphisms"]
    let relation = ["Relations";"Relation_Definitions"], "relation"
  end

  module G = GlobalBindings(Consts)

  include G
  include Consts
  let inverse env evd car rel = 
    type_app_poly env evd coq_inverse [| car ; car; mkProp; rel |]
      (* app_poly evd coq_inverse [| car ; car; mkProp; rel |] *)

end

module TypeGlobal = struct
  module Consts = 
    struct 
      let relation_classes = ["Classes"; "CRelationClasses"]
      let morphisms = ["Classes"; "CMorphisms"]
      let relation = relation_classes, "crelation"
    end

  module G = GlobalBindings(Consts)
  include G


  let inverse env (evd,cstrs) car rel = 
    let evd, (sort,_) = Evarutil.new_type_evar Evd.univ_flexible evd env in
      app_poly (evd,cstrs) coq_inverse [| car ; car; sort; rel |]

end

let sort_of_rel env evm rel =
  Reductionops.sort_of_arity env evm (Retyping.get_type_of env evm rel)

(** Looking up declared rewrite relations (instances of [RewriteRelation]) *)
let is_applied_rewrite_relation env sigma rels t =
  match kind_of_term t with
  | App (c, args) when Array.length args >= 2 ->
      let head = if isApp c then fst (destApp c) else c in
	if Globnames.is_global (coq_eq_ref ()) head then None
	else
	  (try
	      let params, args = Array.chop (Array.length args - 2) args in
	      let env' = Environ.push_rel_context rels env in
	      let evars, (evar, _) = Evarutil.new_type_evar Evd.univ_flexible sigma env' in
	      let evars, inst = 
		app_poly (evars,Evar.Set.empty)
		  TypeGlobal.rewrite_relation_class [| evar; mkApp (c, params) |] in
	      let _ = Typeclasses.resolve_one_typeclass env' (goalevars evars) inst in
		Some (it_mkProd_or_LetIn t rels)
	  with e when Errors.noncritical e -> None)
  | _ -> None

let _ =
  Hook.set Equality.is_applied_rewrite_relation is_applied_rewrite_relation

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let evd_convertible env evd x y =
  try ignore(Evarconv.the_conv_x env x y evd); true
  with e when Errors.noncritical e -> false

let convertible env evd x y =
  Reductionops.is_conv env evd x y

type hypinfo = {
  cl : clausenv;
  prf : constr;
  car : constr;
  rel : constr;
  sort : bool; (* true = Prop; false = Type *)
  l2r : bool;
  c1 : constr;
  c2 : constr;
  c  : (Tacinterp.interp_sign * Tacexpr.glob_constr_and_expr with_bindings) option;
  abs : (constr * types) option;
  flags : Unification.unify_flags;
}

let get_symmetric_proof b = 
  if b then PropGlobal.get_symmetric_proof else TypeGlobal.get_symmetric_proof

let rec decompose_app_rel env evd t = 
  match kind_of_term t with
  | App (f, args) -> 
      if Array.length args > 1 then 
	let fargs, args = Array.chop (Array.length args - 2) args in
	  mkApp (f, fargs), args
      else 
	let (f', args) = decompose_app_rel env evd args.(0) in
	let ty = Typing.type_of env evd args.(0) in
	let f'' = mkLambda (Name (Id.of_string "x"), ty,
	  mkLambda (Name (Id.of_string "y"), lift 1 ty,
	    mkApp (lift 2 f, [| mkApp (lift 2 f', [| mkRel 2; mkRel 1 |]) |])))
	in (f'', args)
  | _ -> error "The term provided is not an applied relation."

let decompose_applied_relation env origsigma sigma flags orig (c,l) left2right =
  let c' = c in
  let ctype = Typing.type_of env sigma c' in
  let find_rel ty =
    let eqclause = Clenv.make_clenv_binding_env_apply env sigma None (c',ty) l in
    let (equiv, args) = decompose_app_rel env eqclause.evd (Clenv.clenv_type eqclause) in
    let c1 = args.(0) and c2 = args.(1) in 
    let ty1, ty2 =
      Typing.type_of env eqclause.evd c1, Typing.type_of env eqclause.evd c2
    in
      if not (evd_convertible env eqclause.evd ty1 ty2) then None
      else
	let sort = sort_of_rel env eqclause.evd equiv in
	let value = Clenv.clenv_value eqclause in
	let eqclause = { eqclause with evd = Evd.diff eqclause.evd origsigma } in
	  Some { cl=eqclause; prf=value;
		 car=ty1; rel = equiv; sort = Sorts.is_prop sort;
		 l2r=left2right; c1=c1; c2=c2; c=orig; abs=None;
		 flags = flags }
  in
    match find_rel ctype with
    | Some c -> c
    | None ->
	let ctx,t' = Reductionops.splay_prod env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' (List.map (fun (n,t) -> n, None, t) ctx)) with
	| Some c -> c
	| None -> error "The term does not end with an applied homogeneous relation."

let decompose_applied_relation_expr env sigma flags (is, (c,l)) left2right =
  let sigma', cbl = Tacinterp.interp_open_constr_with_bindings is env sigma (c,l) in
    decompose_applied_relation env sigma sigma' flags (Some (is, (c,l))) cbl left2right

let rewrite_db = "rewrite"

let conv_transparent_state = (Id.Pred.empty, Cpred.full)

let _ = 
  Auto.add_auto_init
    (fun () ->
       Auto.create_hint_db false rewrite_db conv_transparent_state true)

let rewrite_transparent_state () =
  Auto.Hint_db.transparent_state (Auto.searchtable_map rewrite_db)

let rewrite_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = full_transparent_state;
  Unification.modulo_delta_in_merge = None;
  Unification.check_applied_meta_types = true;
  Unification.resolve_evars = false;
  Unification.use_pattern_unification = true;
  Unification.use_meta_bound_pattern_unification = true;
  Unification.frozen_evars = Evar.Set.empty;
  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
  Unification.allow_K_in_toplevel_higher_order_unification = true
}

let rewrite2_unif_flags =
  {  Unification.modulo_conv_on_closed_terms = Some conv_transparent_state;
     Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
     Unification.modulo_delta = empty_transparent_state;
     Unification.modulo_delta_types = conv_transparent_state;
     Unification.modulo_delta_in_merge = None;
     Unification.check_applied_meta_types = true;
     Unification.resolve_evars = false;
     Unification.use_pattern_unification = true;
     Unification.use_meta_bound_pattern_unification = true;
     Unification.frozen_evars = Evar.Set.empty;
     Unification.restrict_conv_on_strict_subterms = false;
     Unification.modulo_betaiota = true;
     Unification.modulo_eta = true;
     Unification.allow_K_in_toplevel_higher_order_unification = true
  }

let general_rewrite_unif_flags () = 
  let ts = rewrite_transparent_state () in
    {  Unification.modulo_conv_on_closed_terms = Some ts;
       Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
       Unification.modulo_delta = ts;
       Unification.modulo_delta_types = ts;
       Unification.modulo_delta_in_merge = None;
       Unification.check_applied_meta_types = true;
       Unification.resolve_evars = false;
       Unification.use_pattern_unification = true;
       Unification.use_meta_bound_pattern_unification = true;
       Unification.frozen_evars = Evar.Set.empty;
       Unification.restrict_conv_on_strict_subterms = false;
       Unification.modulo_betaiota = true;
       Unification.modulo_eta = true;
       Unification.allow_K_in_toplevel_higher_order_unification = true }

let refresh_hypinfo env sigma hypinfo =
  if Option.is_empty hypinfo.abs then
    let {l2r=l2r; c=c;cl=cl;flags=flags} = hypinfo in
      match c with
	| Some c ->
	    (* Refresh the clausenv to not get the same meta twice in the goal. *)
	    decompose_applied_relation_expr env sigma flags c l2r;
	| _ -> hypinfo
  else hypinfo

let solve_remaining_by by env prf =
  match by with
  | None -> env, prf
  | Some tac ->
    let indep = clenv_independent env in
    let tac = eval_tactic tac in
    let evd' = 
      List.fold_right (fun mv evd ->
        let ty = Clenv.clenv_nf_meta env (meta_type evd mv) in
	let c,_ = Pfedit.build_by_tactic env.env (ty,Univ.ContextSet.empty) (tclCOMPLETE tac) in
	  meta_assign mv (c, (Conv,TypeNotProcessed)) evd)
      indep env.evd
    in { env with evd = evd' }, prf

let extend_evd sigma ext sigma' =
  Evar.Set.fold (fun i acc ->
    Evd.add acc i (Evarutil.nf_evar_info sigma' (Evd.find sigma' i)))
    ext sigma

let shrink_evd sigma ext =
  Evar.Set.fold (fun i acc -> Evd.remove acc i) ext sigma

let no_constraints cstrs = 
  fun ev _ -> not (Evar.Set.mem ev cstrs)

let poly_inverse sort =
  if sort then PropGlobal.inverse else TypeGlobal.inverse

let unify_eqn env (sigma, cstrs) hypinfo by t =
  if isEvar t then None
  else try
    let {cl=cl; prf=prf; car=car; rel=rel; l2r=l2r; c1=c1; c2=c2; c=c; abs=abs} = 
      !hypinfo in
    let left = if l2r then c1 else c2 in
    let evd' = Evd.merge sigma cl.evd in
    let cl = { cl with evd = evd' } in
    let evd', prf, c1, c2, car, rel =
      match abs with
      | Some (absprf, absprfty) ->
	  let env' = clenv_unify ~flags:rewrite_unif_flags CONV left t cl in
	    env'.evd, prf, c1, c2, car, rel
      | None ->
	  let env' = clenv_unify ~flags:!hypinfo.flags CONV left t cl in
	  let env' = Clenvtac.clenv_pose_dependent_evars true env' in
	  let evd' = Typeclasses.resolve_typeclasses ~filter:(no_constraints cstrs)
	    ~fail:true env'.env env'.evd in
	  let env' = { env' with evd = evd' } in
	  let env', prf = solve_remaining_by by env' (Clenv.clenv_value env') in	   
	  let nf c = Evarutil.nf_evar env'.evd (Clenv.clenv_nf_meta env' c) in
	  let c1 = nf c1 and c2 = nf c2
	  and car = nf car and rel = nf rel
	  and prf = nf prf in
	  let ty1 = Typing.type_of env'.env env'.evd c1
	  and ty2 = Typing.type_of env'.env env'.evd c2
	  in
	    if convertible env env'.evd ty1 ty2 then 
	      (if occur_meta_or_existential prf then
		(hypinfo := refresh_hypinfo env env'.evd !hypinfo;
		 env'.evd, prf, c1, c2, car, rel)
	       else (** Evars have been solved, we can go back to the initial evd,
			but keep the potential refinement of existing evars. *)
		  env'.evd, prf, c1, c2, car, rel)
	    else raise Reduction.NotConvertible
    in
    let evars = evd', Evar.Set.empty in
    let evd, res =
      if l2r then evars, (prf, (car, rel, c1, c2))
      else
	try
	  let evars, symprf = get_symmetric_proof !hypinfo.sort env evars car rel in
	    evars, (mkApp (symprf, [| c1 ; c2 ; prf |]),
		    (car, rel, c2, c1))
	with Not_found ->
	  let evars, rel' = poly_inverse !hypinfo.sort env evars car rel in
	    evars, (prf, (car, rel', c2, c1))
    in Some (evd, res)
  with e when Class_tactics.catchable e -> None

type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

type rewrite_proof = 
  | RewPrf of constr * constr
  | RewCast of cast_kind

let get_opt_rew_rel = function RewPrf (rel, prf) -> Some rel | _ -> None

type rewrite_result_info = {
  rew_car : constr;
  rew_from : constr;
  rew_to : constr;
  rew_prf : rewrite_proof;
  rew_evars : evars;
}

type rewrite_result = rewrite_result_info option

type strategy = Environ.env -> Id.t list -> constr -> types ->
  (bool (* prop *) * constr option) -> evars -> rewrite_result option

let make_eq () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq ())
let make_eq_refl () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq_refl ())

let get_rew_rel r = match r.rew_prf with
  | RewPrf (rel, prf) -> rel
  | RewCast c -> mkApp (make_eq (),[| r.rew_car; r.rew_from; r.rew_to |])

let get_rew_prf r = match r.rew_prf with
  | RewPrf (rel, prf) -> rel, prf 
  | RewCast c ->
    let rel = mkApp (make_eq (), [| r.rew_car |]) in
      rel, mkCast (mkApp (make_eq_refl (), [| r.rew_car; r.rew_from |]),
		   c, mkApp (rel, [| r.rew_from; r.rew_to |]))

let poly_subrelation sort = 
  if sort then PropGlobal.subrelation else TypeGlobal.subrelation

let resolve_subrelation env avoid car rel sort prf rel' res =
  if eq_constr rel rel' then res
  else
    let evars, app = app_poly res.rew_evars (poly_subrelation sort) [|car; rel; rel'|] in
    let evars, subrel = new_cstr_evar evars env app in
    let appsub = mkApp (subrel, [| res.rew_from ; res.rew_to ; prf |]) in
      { res with
	rew_prf = RewPrf (rel', appsub);
	rew_evars = evars }

let resolve_morphism env avoid oldt m ?(fnewt=fun x -> x) args args' (b,cstr) evars =
  let evars, morph_instance, proj, sigargs, m', args, args' =
    let first = match (Array.findi (fun _ b -> not (Option.is_empty b)) args') with
    | Some i -> i
    | None -> invalid_arg "resolve_morphism" in
    let morphargs, morphobjs = Array.chop first args in
    let morphargs', morphobjs' = Array.chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.type_of env (goalevars evars) appm in
    let cstrs = List.map 
      (Option.map (fun r -> r.rew_car, get_opt_rew_rel r.rew_prf)) 
      (Array.to_list morphobjs') 
    in
      (* Desired signature *)
    let evars, appmtype', signature, sigargs = 
      if b then PropGlobal.build_signature evars env appmtype cstrs cstr
      else TypeGlobal.build_signature evars env appmtype cstrs cstr
    in
      (* Actual signature found *)
    let cl_args = [| appmtype' ; signature ; appm |] in
    let evars, app = app_poly evars (if b then PropGlobal.proper_type else TypeGlobal.proper_type)
      cl_args in
    let env' = Environ.push_named
      (Id.of_string "do_subrelation", 
       Some (snd (app_poly evars PropGlobal.do_subrelation [||])), 
       snd (app_poly evars PropGlobal.apply_subrelation [||]))
      env
    in
    let evars, morph = new_cstr_evar evars env' app in
      evars, morph, morph, sigargs, appm, morphobjs, morphobjs'
  in
  let projargs, subst, evars, respars, typeargs =
    Array.fold_left2
      (fun (acc, subst, evars, sigargs, typeargs') x y ->
	let (carrier, relation), sigargs = split_head sigargs in
	  match relation with
	  | Some relation ->
	      let carrier = substl subst carrier
	      and relation = substl subst relation in
	      (match y with
	      | None ->
		  let evars, proof = 
		    (if b then PropGlobal.proper_proof else TypeGlobal.proper_proof) 
		      env evars carrier relation x in
		    [ proof ; x ; x ] @ acc, subst, evars, sigargs, x :: typeargs'
	      | Some r ->
		  [ snd (get_rew_prf r); r.rew_to; x ] @ acc, subst, evars, 
	      sigargs, r.rew_to :: typeargs')
	  | None ->
	      if not (Option.is_empty y) then 
		error "Cannot rewrite the argument of a dependent function";
	      x :: acc, x :: subst, evars, sigargs, x :: typeargs')
      ([], [], evars, sigargs, []) args args'
  in
  let proof = applistc proj (List.rev projargs) in
  let newt = applistc m' (List.rev typeargs) in
    match respars with
	[ a, Some r ] -> evars, proof, a, r, oldt, fnewt newt
      | _ -> assert(false)

let apply_constraint env avoid car rel prf cstr res =
  match snd cstr with
  | None -> res
  | Some r -> resolve_subrelation env avoid car rel (fst cstr) prf r res

let eq_env x y = x == y

let apply_rule hypinfo by loccs : strategy =
  let (nowhere_except_in,occs) = convert_occs loccs in
  let is_occ occ =
    if nowhere_except_in then List.mem occ occs else not (List.mem occ occs) in
  let occ = ref 0 in
    fun env avoid t ty cstr evars ->
      if not (eq_env !hypinfo.cl.env env) then
	hypinfo := refresh_hypinfo env (goalevars evars) !hypinfo;
      let unif = unify_eqn env evars hypinfo by t in
	if not (Option.is_empty unif) then incr occ;
	match unif with
	| Some (evars', (prf, (car, rel, c1, c2))) when is_occ !occ ->
	    begin
	      if eq_constr t c2 then Some None
	      else
		let res = { rew_car = ty; rew_from = c1;
			    rew_to = c2; rew_prf = RewPrf (rel, prf); 
			    rew_evars = evars' }
		in Some (Some (apply_constraint env avoid car rel prf cstr res))
	    end
	| _ -> None

let apply_lemma flags (evm,c) left2right by loccs : strategy =
  fun env avoid t ty cstr evars ->
    let hypinfo = 
      let evars' = Evd.merge (goalevars evars) evm in
	ref (decompose_applied_relation env (goalevars evars) evars'
	       flags None c left2right)
    in
      apply_rule hypinfo by loccs env avoid t ty cstr evars

let make_leibniz_proof c ty r =
  let evars = ref r.rew_evars in
  let prf = 
    match r.rew_prf with
    | RewPrf (rel, prf) -> 
	let rel = e_app_poly evars coq_eq [| ty |] in
	let prf =
	  e_app_poly evars coq_f_equal
		[| r.rew_car; ty;
		   mkLambda (Anonymous, r.rew_car, c);
		   r.rew_from; r.rew_to; prf |]
	in RewPrf (rel, prf)
    | RewCast k -> r.rew_prf
  in
    { rew_car = ty; rew_evars = !evars;
      rew_from = subst1 r.rew_from c; rew_to = subst1 r.rew_to c; rew_prf = prf }

let reset_env env =
  let env' = Global.env_of_context (Environ.named_context_val env) in
    Environ.push_rel_context (Environ.rel_context env) env'
      
let fold_match ?(force=false) env sigma c =
  let (ci, p, c, brs) = destCase c in
  let cty = Retyping.get_type_of env sigma c in
  let dep, pred, exists, (sk,eff) = 
    let env', ctx, body =
      let ctx, pred = decompose_lam_assum p in
      let env' = Environ.push_rel_context ctx env in
	env', ctx, pred
    in
    let sortp = Retyping.get_sort_family_of env' sigma body in
    let sortc = Retyping.get_sort_family_of env sigma cty in
    let dep = not (noccurn 1 body) in
    let pred = if dep then p else
	it_mkProd_or_LetIn (subst1 mkProp body) (List.tl ctx)
    in
    let sk = 
      if sortp == InProp then
	if sortc == InProp then
	  if dep then case_dep_scheme_kind_from_prop
	  else case_scheme_kind_from_prop
	else (
	  if dep
	  then case_dep_scheme_kind_from_type_in_prop
	  else case_scheme_kind_from_type)
      else ((* sortc <> InProp by typing *)
	if dep
	then case_dep_scheme_kind_from_type
	else case_scheme_kind_from_type)
    in 
    let exists = Ind_tables.check_scheme sk ci.ci_ind in
      if exists || force then
	dep, pred, exists, Ind_tables.find_scheme sk ci.ci_ind
      else raise Not_found
  in
  let app =
    let ind, args = Inductive.find_rectype env cty in
    let pars, args = List.chop ci.ci_npar args in
    let meths = List.map (fun br -> br) (Array.to_list brs) in
      applist (mkConst sk, pars @ [pred] @ meths @ args @ [c])
  in 
    sk, (if exists then env else reset_env env), app, eff
      
let unfold_match env sigma sk app =
  match kind_of_term app with
  | App (f', args) when eq_constant (fst (destConst f')) sk ->
      let v = Environ.constant_value_in (Global.env ()) (sk,Univ.Instance.empty)(*FIXME*) in
	Reductionops.whd_beta sigma (mkApp (v, args))
  | _ -> app

let is_rew_cast = function RewCast _ -> true | _ -> false

let coerce env avoid cstr res = 
  let rel, prf = get_rew_prf res in
    apply_constraint env avoid res.rew_car rel prf cstr res

let subterm all flags (s : strategy) : strategy =
  let rec aux env avoid t ty (prop, cstr) evars =
    let cstr' = Option.map (fun c -> (ty, Some c)) cstr in
      match kind_of_term t with
      | App (m, args) ->
	  let rewrite_args success =
	    let args', evars', progress =
	      Array.fold_left
		(fun (acc, evars, progress) arg ->
		  if not (Option.is_empty progress) && not all then (None :: acc, evars, progress)
		  else
		    let argty = Typing.type_of env (goalevars evars) arg in
		    let res = s env avoid arg argty (prop,None) evars in
		      match res with
		      | Some None -> (None :: acc, evars, 
				      if Option.is_empty progress then Some false else progress)
		      | Some (Some r) -> 
			(Some r :: acc, r.rew_evars, Some true)
		      | None -> (None :: acc, evars, progress))
		([], evars, success) args
	    in
	      match progress with
	      | None -> None
	      | Some false -> Some None
	      | Some true ->
		  let args' = Array.of_list (List.rev args') in
		    if Array.exists
		      (function 
			 | None -> false 
			 | Some r -> not (is_rew_cast r.rew_prf)) args'
		    then
		      let evars', prf, car, rel, c1, c2 = 
			resolve_morphism env avoid t m args args' (prop, cstr') evars' 
		      in
		      let res = { rew_car = ty; rew_from = c1;
				  rew_to = c2; rew_prf = RewPrf (rel, prf);
				  rew_evars = evars' } 
		      in Some (Some res)
		    else 
		      let args' = Array.map2
			(fun aorig anew ->
			   match anew with None -> aorig
			   | Some r -> r.rew_to) args args' 
		      in
		      let res = { rew_car = ty; rew_from = t;
				  rew_to = mkApp (m, args'); rew_prf = RewCast DEFAULTcast;
				  rew_evars = evars' }
		      in Some (Some res)

	  in
	    if flags.on_morphisms then
	      let mty = Typing.type_of env (goalevars evars) m in
	      let evars, cstr', m, mty, argsl, args = 
		let argsl = Array.to_list args in
		let lift = if prop then PropGlobal.lift_cstr else TypeGlobal.lift_cstr in
		  match lift env evars argsl m mty None with
		  | Some (evars, cstr', m, mty, args) -> 
		    evars, Some cstr', m, mty, args, Array.of_list args
		  | None -> evars, None, m, mty, argsl, args
	      in
	      let m' = s env avoid m mty (prop, cstr') evars in
		match m' with
		| None -> rewrite_args None (* Standard path, try rewrite on arguments *)
		| Some None -> rewrite_args (Some false)
		| Some (Some r) ->
		    (* We rewrote the function and get a proof of pointwise rel for the arguments.
		       We just apply it. *)
		    let prf = match r.rew_prf with
		      | RewPrf (rel, prf) ->
			let app = if prop then PropGlobal.apply_pointwise 
			  else TypeGlobal.apply_pointwise 
			in
			  RewPrf (app rel argsl, mkApp (prf, args))
		      | x -> x
		    in
		    let res =
		      { rew_car = prod_appvect r.rew_car args;
			rew_from = mkApp(r.rew_from, args); rew_to = mkApp(r.rew_to, args);
			rew_prf = prf; rew_evars = r.rew_evars }
		    in 
		      match prf with
		      | RewPrf (rel, prf) ->
			Some (Some (apply_constraint env avoid res.rew_car
				      rel prf (prop,cstr) res))
		      | _ -> Some (Some res)
	    else rewrite_args None
	      
      | Prod (n, x, b) when noccurn 1 b ->
	  let b = subst1 mkProp b in
	  let tx = Typing.type_of env (goalevars evars) x 
	  and tb = Typing.type_of env (goalevars evars) b in
	  let arr = if prop then PropGlobal.arrow_morphism 
	    else TypeGlobal.arrow_morphism 
	  in
	  let (evars', mor), unfold = arr evars tx tb x b in
	  let res = aux env avoid mor ty (prop,cstr) evars' in
	    (match res with
	    | Some (Some r) -> Some (Some { r with rew_to = unfold r.rew_to })
	    | _ -> res)

      (* 		if x' = None && flags.under_lambdas then *)
      (* 		  let lam = mkLambda (n, x, b) in *)
      (* 		  let lam', occ = aux env lam occ None in *)
      (* 		  let res =  *)
      (* 		    match lam' with *)
      (* 		    | None -> None *)
      (* 		    | Some (prf, (car, rel, c1, c2)) -> *)
      (* 			Some (resolve_morphism env sigma t *)
      (* 				 ~fnewt:unfold_all *)
      (* 				 (Lazy.force coq_all) [| x ; lam |] [| None; lam' |] *)
      (* 				 cstr evars) *)
      (* 		  in res, occ *)
      (* 		else *)

      | Prod (n, dom, codom) ->
	  let lam = mkLambda (n, dom, codom) in
	  let (evars', app), unfold = 
	    if eq_constr ty mkProp then
	      (app_poly evars coq_all [| dom; lam |]), TypeGlobal.unfold_all
	    else 
	      let forall = if prop then PropGlobal.coq_forall else TypeGlobal.coq_forall in
		(app_poly evars forall [| dom; lam |]), TypeGlobal.unfold_forall
	  in
	  let res = aux env avoid app ty (prop,cstr) evars' in
	    (match res with
	     | Some (Some r) -> Some (Some { r with rew_to = unfold r.rew_to })
	     | _ -> res)

(* TODO: real rewriting under binders: introduce x x' (H : R x x') and rewrite with 
   H at any occurrence of x. Ask for (R ==> R') for the lambda. Formalize this.
   B. Barras' idea is to have a context of relations, of length 1, with Σ for gluing
   dependent relations and using projections to get them out.
 *)
      (* | Lambda (n, t, b) when flags.under_lambdas -> *)
      (* 	  let n' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n in *)
      (* 	  let n'' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n' in *)
      (* 	  let n''' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n'' in *)
      (* 	  let rel = new_cstr_evar cstr env (mkApp (Lazy.force coq_relation, [|t|])) in *)
      (* 	  let env' = Environ.push_rel_context [(n'',None,lift 2 rel);(n'',None,lift 1 t);(n', None, t)] env in *)
      (* 	  let b' = s env' avoid b (Typing.type_of env' (goalevars evars) (lift 2 b)) (unlift_cstr env (goalevars evars) cstr) evars in *)
      (* 	    (match b' with *)
      (* 	    | Some (Some r) -> *)
      (* 		let prf = match r.rew_prf with *)
      (* 		  | RewPrf (rel, prf) -> *)
      (* 		      let rel = pointwise_or_dep_relation n' t r.rew_car rel in *)
      (* 		      let prf = mkLambda (n', t, prf) in *)
      (* 			RewPrf (rel, prf) *)
      (* 		  | x -> x *)
      (* 		in *)
      (* 		  Some (Some { r with *)
      (* 		    rew_prf = prf; *)
      (* 		    rew_car = mkProd (n, t, r.rew_car); *)
      (* 		    rew_from = mkLambda(n, t, r.rew_from); *)
      (* 		    rew_to = mkLambda (n, t, r.rew_to) }) *)
      (* 	    | _ -> b') *)

      | Lambda (n, t, b) when flags.under_lambdas ->
	let n' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n in
	let env' = Environ.push_rel (n', None, t) env in
	let bty = Typing.type_of env' (goalevars evars) b in
	let unlift = if prop then PropGlobal.unlift_cstr else TypeGlobal.unlift_cstr in
	let b' = s env' avoid b bty (prop, unlift env evars cstr) evars in
	  (match b' with
	  | Some (Some r) ->
	    let r = match r.rew_prf with
	      | RewPrf (rel, prf) ->
		let point = if prop then PropGlobal.pointwise_or_dep_relation else
		    TypeGlobal.pointwise_or_dep_relation
		in
		let evars, rel = point r.rew_evars n' t r.rew_car rel in
		let prf = mkLambda (n', t, prf) in
		  { r with rew_prf = RewPrf (rel, prf); rew_evars = evars }
	      | x -> r
	    in
	      Some (Some { r with
		rew_car = mkProd (n, t, r.rew_car);
		rew_from = mkLambda(n, t, r.rew_from);
		rew_to = mkLambda (n, t, r.rew_to) })
	  | _ -> b')
	    
      | Case (ci, p, c, brs) ->
	let cty = Typing.type_of env (goalevars evars) c in
	let evars', eqty = app_poly evars coq_eq [| cty |] in
	let cstr' = Some eqty in
	let c' = s env avoid c cty (prop, cstr') evars' in
	let res = 
	  match c' with
	  | Some (Some r) ->
	    let case = mkCase (ci, lift 1 p, mkRel 1, Array.map (lift 1) brs) in
	    let res = make_leibniz_proof case ty r in
	      Some (Some (coerce env avoid (prop,cstr) res))
	  | x ->
	    if Array.for_all (Int.equal 0) ci.ci_cstr_ndecls then
	      let evars', eqty = app_poly evars coq_eq [| ty |] in
	      let cstr = Some eqty in
	      let found, brs' = Array.fold_left 
		(fun (found, acc) br ->
		  if not (Option.is_empty found) then (found, fun x -> lift 1 br :: acc x)
		  else
		    match s env avoid br ty (prop,cstr) evars with
		    | Some (Some r) -> (Some r, fun x -> mkRel 1 :: acc x)
		    | _ -> (None, fun x -> lift 1 br :: acc x))
		(None, fun x -> []) brs
	      in
		match found with
		| Some r ->
		  let ctxc = mkCase (ci, lift 1 p, lift 1 c, Array.of_list (List.rev (brs' x))) in
		    Some (Some (make_leibniz_proof ctxc ty r))
		| None -> x
	    else
	      match try Some (fold_match env (goalevars evars) t) with Not_found -> None with
	      | None -> x
	      | Some (cst, _, t', eff (*FIXME*)) ->
		match aux env avoid t' ty (prop,cstr) evars with
		| Some (Some prf) -> 
		  Some (Some { prf with
		    rew_from = t; 
		    rew_to = unfold_match env (goalevars evars) cst prf.rew_to })
		| x' -> x
	in 
	  (match res with
	  | Some (Some r) ->  
	    let rel, prf = get_rew_prf r in
	      Some (Some (apply_constraint env avoid r.rew_car rel prf (prop,cstr) r))
	  | x -> x)
      | _ -> None
  in aux

let all_subterms = subterm true default_flags
let one_subterm = subterm false default_flags

(** Requires transitivity of the rewrite step, if not a reduction.
    Not tail-recursive. *)

let transitivity env avoid prop (res : rewrite_result_info) (next : strategy) : 
    rewrite_result option =
  let nextres =
    next env avoid res.rew_to res.rew_car
      (prop, get_opt_rew_rel res.rew_prf) res.rew_evars 
  in 
  match nextres with
  | None -> None
  | Some None -> Some (Some res)
  | Some (Some res') ->
      match res.rew_prf with
      | RewCast c -> Some (Some { res' with rew_from = res.rew_from })
      | RewPrf (rew_rel, rew_prf) ->
	  match res'.rew_prf with
	  | RewCast _ -> Some (Some ({ res with rew_to = res'.rew_to }))
	  | RewPrf (res'_rel, res'_prf) ->
	    let trans = 
	      if prop then PropGlobal.transitive_type 
	      else TypeGlobal.transitive_type
	    in
	    let evars, prfty = 
	      app_poly res'.rew_evars trans [| res.rew_car; rew_rel |] 
	    in
	    let evars, prf = new_cstr_evar evars env prfty in
	    let prf = mkApp (prf, [|res.rew_from; res'.rew_from; res'.rew_to;
				    rew_prf; res'_prf |])
	    in Some (Some { res' with rew_from = res.rew_from; 
	      rew_evars = evars; rew_prf = RewPrf (res'_rel, prf) })
		
(** Rewriting strategies.

    Inspired by ELAN's rewriting strategies:
    http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.4049
*)

module Strategies =
  struct

    let fail : strategy =
      fun env avoid t ty cstr evars -> None

    let id : strategy =
      fun env avoid t ty cstr evars -> Some None

    let refl : strategy =
      fun env avoid t ty (prop,cstr) evars ->
	let evars, rel = match cstr with
	  | None -> 
	    let mkr = if prop then PropGlobal.mk_relation else TypeGlobal.mk_relation in
	    let evars, rty = mkr evars ty in
	      new_cstr_evar evars env rty
	  | Some r -> evars, r
	in
	let evars, proof =
	  let proxy = 
	    if prop then PropGlobal.proper_proxy_type 
	    else TypeGlobal.proper_proxy_type
	  in
	  let evars, mty = app_poly evars proxy [| ty ; rel; t |] in
	    new_cstr_evar evars env mty
	in
	  Some (Some { rew_car = ty; rew_from = t; rew_to = t;
		       rew_prf = RewPrf (rel, proof); rew_evars = evars })

    let progress (s : strategy) : strategy =
      fun env avoid t ty cstr evars ->
	match s env avoid t ty cstr evars with
	| None -> None
	| Some None -> None
	| r -> r

    let seq first snd : strategy =
      fun env avoid t ty cstr evars ->
	match first env avoid t ty cstr evars with
	| None -> None
	| Some None -> snd env avoid t ty cstr evars
	| Some (Some res) -> transitivity env avoid (fst cstr) res snd

    let choice fst snd : strategy =
      fun env avoid t ty cstr evars ->
	match fst env avoid t ty cstr evars with
	| None -> snd env avoid t ty cstr evars
	| res -> res

    let try_ str : strategy = choice str id

    let fix (f : strategy -> strategy) : strategy =
      let rec aux env = f (fun env -> aux env) env in aux

    let any (s : strategy) : strategy =
      fix (fun any -> try_ (seq s any))

    let repeat (s : strategy) : strategy =
      seq s (any s)

    let bu (s : strategy) : strategy =
      fix (fun s' -> seq (choice (progress (all_subterms s')) s) (try_ s'))

    let td (s : strategy) : strategy =
      fix (fun s' -> seq (choice s (progress (all_subterms s'))) (try_ s'))

    let innermost (s : strategy) : strategy =
      fix (fun ins -> choice (one_subterm ins) s)

    let outermost (s : strategy) : strategy =
      fix (fun out -> choice s (one_subterm out))

    let lemmas flags cs : strategy =
      List.fold_left (fun tac (l,l2r,by) ->
	choice tac (apply_lemma flags l l2r by AllOccurrences))
	fail cs

    let inj_open hint =
      (Evd.from_env ~ctx:hint.Autorewrite.rew_ctx (Global.env()),
       (hint.Autorewrite.rew_lemma, NoBindings))

    let old_hints (db : string) : strategy =
      let rules = Autorewrite.find_rewrites db in
	lemmas rewrite_unif_flags
	  (List.map (fun hint -> (inj_open hint, hint.Autorewrite.rew_l2r,
				  hint.Autorewrite.rew_tac)) rules)

    let hints (db : string) : strategy =
      fun env avoid t ty cstr evars ->
      let rules = Autorewrite.find_matches db t in
      let lemma hint = (inj_open hint, hint.Autorewrite.rew_l2r,
			hint.Autorewrite.rew_tac) in
      let lems = List.map lemma rules in
	lemmas rewrite_unif_flags lems env avoid t ty cstr evars

    let reduce (r : Redexpr.red_expr) : strategy =
      let rfn, ckind = Redexpr.reduction_of_red_expr r in
	fun env avoid t ty cstr evars ->
	  let t' = rfn env (goalevars evars) t in
	    if eq_constr t' t then
	      Some None
	    else
	      Some (Some { rew_car = ty; rew_from = t; rew_to = t';
			   rew_prf = RewCast ckind; 
			   rew_evars = evars })
	
    let fold c : strategy =
      fun env avoid t ty cstr evars ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Constrintern.interp_open_constr (goalevars evars) env c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when Errors.noncritical e ->
            error "fold: the term is not unfoldable !"
	in
	  try
	  let sigma = Unification.w_unify env sigma CONV ~flags:(Unification.elim_flags ())
	    unfolded t in
	    let c' = Evarutil.nf_evar sigma c in
	      Some (Some { rew_car = ty; rew_from = t; rew_to = c';
			   rew_prf = RewCast DEFAULTcast; 
			   rew_evars = (sigma, snd evars) })
	  with e when Errors.noncritical e -> None

    let fold_glob c : strategy =
      fun env avoid t ty cstr evars ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Pretyping.understand_tcc (goalevars evars) env c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when Errors.noncritical e ->
            error "fold: the term is not unfoldable !"
	in
	  try
	    let sigma = Unification.w_unify env sigma CONV ~flags:(Unification.elim_flags ()) unfolded t in
	    let c' = Evarutil.nf_evar sigma c in
	      Some (Some { rew_car = ty; rew_from = t; rew_to = c';
			   rew_prf = RewCast DEFAULTcast; 
			   rew_evars = (sigma, snd evars) })
	  with e when Errors.noncritical e -> None
  

end

(** The strategy for a single rewrite, dealing with occurences. *)

let rewrite_strat flags occs hyp =
  let app = apply_rule hyp None occs in
  let rec aux () =
    Strategies.choice app (subterm true flags (fun env -> aux () env))
  in aux ()

let get_hypinfo_ids {c = opt} =
  match opt with
  | None -> []
  | Some (is, gc) ->
    let avoid = Option.default [] (TacStore.get is.extra f_avoid_ids) in
      Id.Map.fold (fun id _ accu -> id :: accu) is.lfun avoid
      
let rewrite_with flags c left2right loccs : strategy =
  fun env avoid t ty cstr evars ->
    let gevars = goalevars evars in
    let hypinfo = ref (decompose_applied_relation_expr env gevars flags c left2right) in
    let avoid = get_hypinfo_ids !hypinfo @ avoid in
      rewrite_strat default_flags loccs hypinfo env avoid t ty cstr (gevars, cstrevars evars)

let apply_strategy (s : strategy) env avoid concl (prop, cstr) evars =
  let res =
    s env avoid concl (Typing.type_of env (goalevars evars) concl)
      (prop, Some cstr) evars
  in
    match res with
    | None -> None
    | Some None -> Some None
    | Some (Some res) ->
	Some (Some (res.rew_prf, res.rew_evars, res.rew_car, res.rew_from, res.rew_to))

let solve_constraints env (evars,cstrs) =
  Typeclasses.resolve_typeclasses env ~split:false ~fail:true evars

let nf_zeta =
  Reductionops.clos_norm_flags (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])

let map_rewprf f = function
  | RewPrf (rel, prf) -> RewPrf (f rel, f prf)
  | RewCast c -> RewCast c

exception RewriteFailure of std_ppcmds

type result = (evar_map * constr option * types) option option

let cl_rewrite_clause_aux ?(abs=None) strat env avoid sigma concl is_hyp : result =
  let evars = (sigma, Evar.Set.empty) in
  let evars, cstr =
    let sort = Typing.sort_of env (goalevars evars) concl in
    let prop, (evars, arrow) = 
      if is_prop_sort sort then true, app_poly evars impl [||]
      else false, app_poly evars arrow [||]
    in
      match is_hyp with
      | None -> 
	let evars, t = poly_inverse prop env evars (mkSort sort) arrow in 
	  evars, (prop, t)
      | Some _ -> evars, (prop, arrow)
  in
  let eq = apply_strategy strat env avoid concl cstr evars in
    match eq with
    | Some (Some (p, (evars, cstrs), car, oldt, newt)) ->
	let evars' = solve_constraints env (evars, cstrs) in
	let p = map_rewprf (fun p -> nf_zeta env evars' (Evarutil.nf_evar evars' p)) p in
	let newt = Evarutil.nf_evar evars' newt in
	let abs = Option.map (fun (x, y) ->
				Evarutil.nf_evar evars' x, Evarutil.nf_evar evars' y) abs in
	let evars = (* Keep only original evars (potentially instantiated) and goal evars,
		       the rest has been defined and substituted already. *)
	  Evar.Set.fold (fun ev acc -> Evd.remove acc ev) cstrs evars'
	in
	let res =
	  match is_hyp with
	  | Some id ->
	      (match p with
	       | RewPrf (rel, p) ->
		   let term =
		     match abs with
		     | None -> p
		     | Some (t, ty) ->
			 mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |])
		   in
		     Some (evars, Some (mkApp (term, [| mkVar id |])), newt)
	       | RewCast c ->
		   Some (evars, None, newt))
		
	  | None ->
	      (match p with
	       | RewPrf (rel, p) ->
		   (match abs with
		    | None -> Some (evars, Some p, newt)
		    | Some (t, ty) ->
			let proof = mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |]) in
			  Some (evars, Some proof, newt))
	       | RewCast c -> Some (evars, None, newt))
	in Some res
    | Some None -> Some None
    | None -> None
		   
let rewrite_refine (evd,c) = 
  Tacmach.refine c

let cl_rewrite_clause_tac ?abs strat meta clause gl =
  let evartac evd = Refiner.tclEVARS (Evd.clear_metas evd) in
  let treat res =
    match res with
    | None -> tclFAIL 0 (str "Nothing to rewrite")
    | Some None -> tclIDTAC
    | Some (Some (undef, p, newt)) ->
	let tac = 
	  match clause, p with
	  | Some id, Some p ->
	      cut_replacing id newt (Tacmach.refine p)
	  | Some id, None -> 
	      change_in_hyp None newt (id, InHypTypeOnly)
	  | None, Some p ->
	      let name = next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
		tclTHENLAST
		  (Tacmach.internal_cut false name newt)
		  (tclTHEN (Tactics.revert [name]) (Tacmach.refine p))
	  | None, None -> change_in_concl None newt
	in tclTHEN (evartac undef) tac
  in
  let tac =
    try
      let concl, is_hyp =
	match clause with
	| Some id -> pf_get_hyp_typ gl id, Some id
	| None -> pf_concl gl, None
      in
      let sigma = project gl in
      let concl = Evarutil.nf_evar sigma concl in 
      let res = cl_rewrite_clause_aux ?abs strat (pf_env gl) [] sigma concl is_hyp in
	treat res
    with
    | TypeClassError (env, (UnsatisfiableConstraints _ as e)) ->
	Refiner.tclFAIL 0
	  (str"Unable to satisfy the rewriting constraints."
	   ++ fnl () ++ Himsg.explain_typeclass_error env e)
  in tac gl


let bind_gl_info f =
  bind concl (fun c -> bind env (fun v -> bind defs (fun ev -> f c v ev))) 

let fail l s = Refiner.tclFAIL l s

let new_refine c : Goal.subgoals Goal.sensitive =
  let refable = Goal.Refinable.make
    (fun handle -> Goal.Refinable.constr_of_open_constr handle true c) 
  in Goal.bind refable Goal.refine

let assert_replacing id newt tac = 
  let sens = bind_gl_info 
    (fun concl env sigma ->
       let nc' = 
	 Environ.fold_named_context
	   (fun _ (n, b, t as decl) nc' ->
	      if Id.equal n id then (n, b, newt) :: nc'
	      else decl :: nc')
	   env ~init:[]
       in
       let reft = Refinable.make 
	 (fun h -> 
	    Goal.bind (Refinable.mkEvar h
			 (Environ.reset_with_named_context (val_of_named_context nc') env) concl)
	      (fun ev -> 
		 Goal.bind (Refinable.mkEvar h env newt)
		   (fun ev' ->
		      let inst = 
			fold_named_context
			  (fun _ (n, b, t) inst ->
			     if Id.equal n id then ev' :: inst
			     else if Option.is_empty b then mkVar n :: inst else inst)
			  env ~init:[]
		      in
		      let (e, args) = destEvar ev in
			Goal.return (mkEvar (e, Array.of_list inst)))))
       in Goal.bind reft Goal.refine)
  in Proofview.tclTHEN (Proofview.tclSENSITIVE sens) 
       (Proofview.tclFOCUS 2 2 tac)

let newfail n s = 
  Proofview.tclZERO (Refiner.FailError (n, lazy s))

let cl_rewrite_clause_newtac ?abs strat clause =
  let treat (res, is_hyp) = 
    match res with
    | None -> newfail 0 (str "Nothing to rewrite")
    | Some None -> Proofview.tclUNIT ()
    | Some (Some res) ->
	match is_hyp, res with
	| Some id, (undef, Some p, newt) ->
	    assert_replacing id newt (Proofview.tclSENSITIVE (new_refine (undef, p)))
	| Some id, (undef, None, newt) -> 
	    Proofview.tclSENSITIVE (Goal.convert_hyp false (id, None, newt))
	| None, (undef, Some p, newt) ->
	    let refable = Goal.Refinable.make
	      (fun handle -> 
		 Goal.bind env
		   (fun env -> Goal.bind (Refinable.mkEvar handle env newt)
		      (fun ev ->
			 Goal.Refinable.constr_of_open_constr handle true 
			   (undef, mkApp (p, [| ev |])))))
	    in
	      Proofview.tclSENSITIVE (Goal.bind refable Goal.refine)
	| None, (undef, None, newt) ->
	    Proofview.tclSENSITIVE (Goal.convert_concl false newt)
  in
  let info =
    bind_gl_info
      (fun concl env sigma ->
	 let ty, is_hyp =
	   match clause with
	   | Some id -> Environ.named_type id env, Some id
	   | None -> concl, None
	 in
	   try 
	     let res = 
	       cl_rewrite_clause_aux ?abs strat env [] sigma ty is_hyp 
	     in return (res, is_hyp)
	   with
	   | TypeClassError (env, (UnsatisfiableConstraints _ as e)) ->
	     raise (RewriteFailure (str"Unable to satisfy the rewriting constraints."
			++ fnl () ++ Himsg.explain_typeclass_error env e)))
  in Proofview.tclGOALBINDU info (fun i -> treat i)
  
let newtactic_init_setoid () = 
  try init_setoid (); Proofview.tclUNIT ()
  with e when Errors.noncritical e -> Proofview.tclZERO e

let tactic_init_setoid () = 
  init_setoid (); tclIDTAC
  
let cl_rewrite_clause_new_strat ?abs strat clause =
  Proofview.tclTHEN (newtactic_init_setoid ())
  (try cl_rewrite_clause_newtac ?abs strat clause
   with RewriteFailure s ->
   newfail 0 (str"setoid rewrite failed: " ++ s))

(* let cl_rewrite_clause_newtac' l left2right occs clause = *)
(*   Proof_global.run_tactic  *)
(*     (Proofview.tclFOCUS 1 1  *)
(*        (cl_rewrite_clause_new_strat (rewrite_with rewrite_unif_flags l left2right occs) clause)) *)

let cl_rewrite_clause_strat strat clause =
  tclTHEN (tactic_init_setoid ())
  (fun gl -> 
   let meta = Evarutil.new_meta() in
     (*     let gl = { gl with sigma = Typeclasses.mark_unresolvables gl.sigma } in *)
     try cl_rewrite_clause_tac strat (mkMeta meta) clause gl
     with RewriteFailure e ->
       tclFAIL 0 (str"setoid rewrite failed: " ++ e) gl
     | Refiner.FailError (n, pp) -> 
       tclFAIL n (str"setoid rewrite failed: " ++ Lazy.force pp) gl)

let cl_rewrite_clause l left2right occs clause gl =
  cl_rewrite_clause_strat (rewrite_with (general_rewrite_unif_flags ()) l left2right occs) clause gl


let occurrences_of = function
  | n::_ as nl when n < 0 -> (false,List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
	error "Illegal negative occurrence number.";
      (true,nl)

open Extraargs

let apply_constr_expr c l2r occs = fun env avoid t ty cstr evars ->
  let evd, c = Constrintern.interp_open_constr (goalevars evars) env c in
    apply_lemma (general_rewrite_unif_flags ()) (Evd.empty, (c, NoBindings)) 
      l2r None occs env avoid t ty cstr (evd, cstrevars evars)

let apply_glob_constr c l2r occs = fun env avoid t ty cstr evars ->
  let evd, c = (Pretyping.understand_tcc (goalevars evars) env c) in
    apply_lemma (general_rewrite_unif_flags ()) (Evd.empty, (c, NoBindings)) 
      l2r None occs env avoid t ty cstr (evd, cstrevars evars)

let interp_constr_list env sigma =
  List.map (fun c -> 
	      let evd, c = Constrintern.interp_open_constr sigma env c in
		(evd, (c, NoBindings)), true, None)

let interp_glob_constr_list env sigma =
  List.map (fun c -> 
	      let evd, c = Pretyping.understand_tcc sigma env c in
		(evd, (c, NoBindings)), true, None)

(* Syntax for rewriting with strategies *)

type ('constr,'redexpr) strategy_ast = 
  | StratId | StratFail | StratRefl
  | StratUnary of string * ('constr,'redexpr) strategy_ast
  | StratBinary of string * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratConstr of 'constr * bool
  | StratTerms of 'constr list
  | StratHints of bool * string
  | StratEval of 'redexpr 
  | StratFold of 'constr

let rec map_strategy (f : 'a -> 'a2) (g : 'b -> 'b2) : ('a,'b) strategy_ast -> ('a2,'b2) strategy_ast = function
  | StratId | StratFail | StratRefl as s -> s
  | StratUnary (s, str) -> StratUnary (s, map_strategy f g str)
  | StratBinary (s, str, str') -> StratBinary (s, map_strategy f g str, map_strategy f g str')
  | StratConstr (c, b) -> StratConstr (f c, b)
  | StratTerms l -> StratTerms (List.map f l)
  | StratHints (b, id) -> StratHints (b, id)
  | StratEval r -> StratEval (g r)
  | StratFold c -> StratFold (f c)

let rec strategy_of_ast = function
  | StratId -> Strategies.id
  | StratFail -> Strategies.fail
  | StratRefl -> Strategies.refl
  | StratUnary (f, s) -> 
    let s' = strategy_of_ast s in
    let f' = match f with
      | "subterms" -> all_subterms
      | "subterm" -> one_subterm
      | "innermost" -> Strategies.innermost
      | "outermost" -> Strategies.outermost
      | "bottomup" -> Strategies.bu
      | "topdown" -> Strategies.td
      | "progress" -> Strategies.progress
      | "try" -> Strategies.try_
      | "any" -> Strategies.any
      | "repeat" -> Strategies.repeat
      | _ -> anomaly ~label:"strategy_of_ast" (str"Unkwnon strategy: " ++ str f)
    in f' s'
  | StratBinary (f, s, t) ->
    let s' = strategy_of_ast s in
    let t' = strategy_of_ast t in
    let f' = match f with
      | "compose" -> Strategies.seq
      | "choice" -> Strategies.choice
      | _ -> anomaly ~label:"strategy_of_ast" (str"Unkwnon strategy: " ++ str f)
    in f' s' t'
  | StratConstr (c, b) -> apply_glob_constr (fst c) b AllOccurrences
  | StratHints (old, id) -> if old then Strategies.old_hints id else Strategies.hints id
  | StratTerms l -> 
    (fun env avoid t ty cstr evars ->
     let l' = interp_glob_constr_list env (goalevars evars) (List.map fst l) in
       Strategies.lemmas rewrite_unif_flags l' env avoid t ty cstr evars)
  | StratEval r -> 
    (fun env avoid t ty cstr evars ->
     let (sigma,r_interp) = Tacinterp.interp_redexp env (goalevars evars) r in
       Strategies.reduce r_interp env avoid t ty cstr (sigma,cstrevars evars))
  | StratFold c -> Strategies.fold_glob (fst c)


(* By default the strategy for "rewrite_db" is top-down *)

let mkappc s l = CAppExpl (Loc.ghost,(None,(Libnames.Ident (Loc.ghost,Id.of_string s)),None),l)

let declare_an_instance n s args =
  ((Loc.ghost,Name n), Explicit,
  CAppExpl (Loc.ghost, (None, Qualid (Loc.ghost, qualid_of_string s),None),
	   args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance global binders instance fields =
  new_instance (Flags.is_universe_polymorphism ()) 
    binders instance (Some (CRecord (Loc.ghost,None,fields)))
    ~global ~generalize:false None

let declare_instance_refl global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Reflexive") "Coq.Classes.RelationClasses.Reflexive"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "reflexivity"),lemma)]

let declare_instance_sym global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Symmetric") "Coq.Classes.RelationClasses.Symmetric"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "symmetry"),lemma)]

let declare_instance_trans global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Transitive") "Coq.Classes.RelationClasses.Transitive"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "transitivity"),lemma)]

let declare_relation ?(binders=[]) a aeq n refl symm trans =
  init_setoid ();
  let global = not (Locality.make_section_locality (Locality.LocalityFixme.consume ())) in
  let instance = declare_instance a aeq (add_suffix n "_relation") "Coq.Classes.RelationClasses.RewriteRelation"
  in ignore(anew_instance global binders instance []);
  match (refl,symm,trans) with
      (None, None, None) -> ()
    | (Some lemma1, None, None) ->
	ignore (declare_instance_refl global binders a aeq n lemma1)
    | (None, Some lemma2, None) ->
	ignore (declare_instance_sym global binders a aeq n lemma2)
    | (None, None, Some lemma3) ->
	ignore (declare_instance_trans global binders a aeq n lemma3)
    | (Some lemma1, Some lemma2, None) ->
	ignore (declare_instance_refl global binders a aeq n lemma1);
	ignore (declare_instance_sym global binders a aeq n lemma2)
    | (Some lemma1, None, Some lemma3) ->
	let _lemma_refl = declare_instance_refl global binders a aeq n lemma1 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PreOrder"
	in ignore(
	    anew_instance global binders instance
	      [(Ident (Loc.ghost,Id.of_string "PreOrder_Reflexive"), lemma1);
	       (Ident (Loc.ghost,Id.of_string "PreOrder_Transitive"),lemma3)])
    | (None, Some lemma2, Some lemma3) ->
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PER"
	in ignore(
	    anew_instance global binders instance
	      [(Ident (Loc.ghost,Id.of_string "PER_Symmetric"), lemma2);
	       (Ident (Loc.ghost,Id.of_string "PER_Transitive"),lemma3)])
     | (Some lemma1, Some lemma2, Some lemma3) ->
	let _lemma_refl = declare_instance_refl global binders a aeq n lemma1 in
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
	in ignore(
	  anew_instance global binders instance
	    [(Ident (Loc.ghost,Id.of_string "Equivalence_Reflexive"), lemma1);
	     (Ident (Loc.ghost,Id.of_string "Equivalence_Symmetric"), lemma2);
	     (Ident (Loc.ghost,Id.of_string "Equivalence_Transitive"), lemma3)])

let cHole = CHole (Loc.ghost, None)

let proper_projection r ty =
  let ctx, inst = decompose_prod_assum ty in
  let mor, args = destApp inst in
  let instarg = mkApp (r, rel_vect 0 (List.length ctx)) in
  let app = mkApp (Lazy.force PropGlobal.proper_proj,
		  Array.append args [| instarg |]) in
    it_mkLambda_or_LetIn app ctx

let declare_projection n instance_id r =
  let c,uctx = Universes.fresh_global_instance (Global.env()) r in
  let poly = Global.is_polymorphic r in
  let ty = Retyping.get_type_of (Global.env ()) Evd.empty c in
  let term = proper_projection c ty in
  let typ = Typing.type_of (Global.env ()) Evd.empty term in
  let ctx, typ = decompose_prod_assum typ in
  let typ =
    let n =
      let rec aux t =
	match kind_of_term t with
	| App (f, [| a ; a' ; rel; rel' |]) 
	    when Globnames.is_global (PropGlobal.respectful_ref ()) f ->
	  succ (aux rel')
	| _ -> 0
      in
      let init =
	match kind_of_term typ with
	    App (f, args) when Globnames.is_global (PropGlobal.respectful_ref ()) f  ->
	      mkApp (f, fst (Array.chop (Array.length args - 2) args))
	  | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.splay_prod_n (Global.env()) Evd.empty (3 * n) typ
    in it_mkProd_or_LetIn ccl ctx
  in
  let typ = it_mkProd_or_LetIn typ ctx in
  let cst = 
    Declare.definition_entry ~types:typ ~poly ~univs:(Univ.ContextSet.to_context uctx) 
      term 
  in
    ignore(Declare.declare_constant n 
	   (Entries.DefinitionEntry cst, Decl_kinds.IsDefinition Decl_kinds.Definition))

let build_morphism_signature m =
  let env = Global.env () in
  let m,ctx = Constrintern.interp_constr Evd.empty env m in
  let sigma = Evd.from_env ~ctx env in
  let t = Typing.type_of env sigma m in
  let cstrs =
    let rec aux t =
      match kind_of_term t with
	| Prod (na, a, b) ->
	    None :: aux b
	| _ -> []
    in aux t
  in
  let evars, t', sig_, cstrs = 
    PropGlobal.build_signature (Evd.empty, Evar.Set.empty) env t cstrs None in
  let evd = ref evars in
  let _ = List.iter
    (fun (ty, rel) ->
      Option.iter (fun rel ->
	let default = e_app_poly evd PropGlobal.default_relation [| ty; rel |] in
	  ignore(e_new_cstr_evar evd env default))
	rel)
    cstrs
  in
  let morph = e_app_poly evd PropGlobal.proper_type [| t; sig_; m |] in
  let evd = solve_constraints env !evd in
  let m = Evarutil.nf_evar evd morph in
    Evarutil.check_evars env Evd.empty evd m; m

let default_morphism sign m =
  let env = Global.env () in
  let t = Typing.type_of env Evd.empty m in
  let evars, _, sign, cstrs =
    PropGlobal.build_signature (Evd.empty, Evar.Set.empty) env t (fst sign) (snd sign)
  in
  let evars, morph = app_poly evars PropGlobal.proper_type [| t; sign; m |] in
  let evars, mor = resolve_one_typeclass env (goalevars evars) morph in
    mor, proper_projection mor morph

let add_setoid global binders a aeq t n =
  init_setoid ();
  let _lemma_refl = declare_instance_refl global binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in
  let _lemma_sym = declare_instance_sym global binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let _lemma_trans = declare_instance_trans global binders a aeq n (mkappc "Seq_trans" [a;aeq;t]) in
  let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
  in ignore(
    anew_instance global binders instance
      [(Ident (Loc.ghost,Id.of_string "Equivalence_Reflexive"), mkappc "Seq_refl" [a;aeq;t]);
       (Ident (Loc.ghost,Id.of_string "Equivalence_Symmetric"), mkappc "Seq_sym" [a;aeq;t]);
       (Ident (Loc.ghost,Id.of_string "Equivalence_Transitive"), mkappc "Seq_trans" [a;aeq;t])])


let make_tactic name =
  let open Tacexpr in
  let loc = Loc.ghost in
  let tacpath = Libnames.qualid_of_string name in
  let tacname = Qualid (loc, tacpath) in
  TacArg (loc, TacCall (loc, tacname, []))

let add_morphism_infer glob m n =
  init_setoid ();
  let poly = Flags.is_universe_polymorphism () in
  let instance_id = add_suffix n "_Proper" in
  let instance = build_morphism_signature m in
  let ctx = Univ.ContextSet.empty (*FIXME *) in
    if Lib.is_modtype () then
      let cst = Declare.declare_constant ~internal:Declare.KernelSilent instance_id
				(Entries.ParameterEntry 
				 (None,poly,(instance,Univ.UContext.empty),None), 
				 Decl_kinds.IsAssumption Decl_kinds.Logical)
      in
	add_instance (Typeclasses.new_instance 
			(Lazy.force PropGlobal.proper_class) None glob 
			poly (ConstRef cst));
	declare_projection n instance_id (ConstRef cst)
    else
      let kind = Decl_kinds.Global, poly, 
	Decl_kinds.DefinitionBody Decl_kinds.Instance 
      in
      let tac = make_tactic "Coq.Classes.SetoidTactics.add_morphism_tactic" in
      let hook _ _ = function
	| Globnames.ConstRef cst ->
	  add_instance (Typeclasses.new_instance 
			  (Lazy.force PropGlobal.proper_class) None
			  glob poly (ConstRef cst));
	  declare_projection n instance_id (ConstRef cst)
	| _ -> assert false
      in
	Flags.silently
	  (fun () ->
	    Lemmas.start_proof instance_id kind (instance, ctx) (Some hook);
	    Pfedit.by (Tacinterp.interp tac)) ()

let add_morphism glob binders m s n =
  init_setoid ();
  let poly = Flags.is_universe_polymorphism () in
  let instance_id = add_suffix n "_Proper" in
  let instance =
    ((Loc.ghost,Name instance_id), Explicit,
    CAppExpl (Loc.ghost,
	     (None, Qualid (Loc.ghost, Libnames.qualid_of_string "Coq.Classes.Morphisms.Proper"),None),
	     [cHole; s; m]))
  in
  let tac = Tacinterp.interp (make_tactic "add_morphism_tactic") in
    ignore(new_instance ~global:glob poly binders instance (Some (CRecord (Loc.ghost,None,[])))
	      ~generalize:false ~tac ~hook:(declare_projection n instance_id) None)

(** Bind to "rewrite" too *)

(** Taken from original setoid_replace, to emulate the old rewrite semantics where
    lemmas are first instantiated and then rewrite proceeds. *)

let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise
	(Logic.RefinerError (Logic.UnresolvedBindings [Evd.meta_name evd m])))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,({Evd.rebus=rebus1; Evd.freemetas=freemetas1},_),
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas

let unification_rewrite flags l2r c1 c2 cl car rel but gl =
  let env = pf_env gl in
  let evd = Evd.merge (project gl) cl.evd in
  let (evd',c') =
    try
      (* ~flags:(false,true) to allow to mark occurrences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm 
       ~flags:{ rewrite_unif_flags with Unification.resolve_evars = true } env
        evd ((if l2r then c1 else c2),but)
    with
	Pretype_errors.PretypeError _ ->
	  (* ~flags:(true,true) to make Ring work (since it really
             exploits conversion) *)
	  Unification.w_unify_to_subterm 
	  ~flags:{ flags with Unification.resolve_evars = true }
	    env evd ((if l2r then c1 else c2),but)
  in
  let cl' = {cl with evd = evd'} in
  let cl' = Clenvtac.clenv_pose_dependent_evars true cl' in
  let nf c = Evarutil.nf_evar cl'.evd (Clenv.clenv_nf_meta cl' c) in
  let c1 = if l2r then nf c' else nf c1
  and c2 = if l2r then nf c2 else nf c'
  and car = nf car and rel = nf rel in
  check_evar_map_of_evars_defs cl'.evd;
  let prf = nf (Clenv.clenv_value cl') and prfty = nf (Clenv.clenv_type cl') in
  let sort = sort_of_rel env evd' (pf_concl gl) in
  let cl' = { cl' with templval = mk_freelisted prf ; templtyp = mk_freelisted prfty;
    evd = Evd.diff cl'.evd (project gl) } 
  in
    {cl=cl'; prf=(mkRel 1); car=car; rel=rel; l2r=l2r; 
     c1=c1; c2=c2; c=None; abs=Some (prf, prfty); sort = Sorts.is_prop sort; flags = flags}

let get_hyp gl evars (c,l) clause l2r =
  let flags = rewrite2_unif_flags in
  let hi = decompose_applied_relation (pf_env gl) evars evars flags None (c,l) l2r in
  let but = match clause with
    | Some id -> pf_get_hyp_typ gl id 
    | None -> Evarutil.nf_evar evars (pf_concl gl)
  in
  let unif = unification_rewrite flags hi.l2r hi.c1 hi.c2 hi.cl hi.car hi.rel but gl in
    { unif with flags = rewrite_unif_flags }

let general_rewrite_flags = { under_lambdas = false; on_morphisms = true }

let apply_lemma gl (c,l) cl l2r occs =
  let sigma = project gl in
  let hypinfo = ref (get_hyp gl sigma (c,l) cl l2r) in
  let app = apply_rule hypinfo None occs in
  let rec aux () =
    Strategies.choice app (subterm true general_rewrite_flags (fun env -> aux () env))
  in !hypinfo, aux ()


let cl_rewrite_clause_tac abs strat meta cl gl =
  cl_rewrite_clause_tac ~abs strat meta cl gl

(* let rewriteclaustac_key = Profile.declare_profile "cl_rewrite_clause_tac";; *)
(* let cl_rewrite_clause_tac = Profile.profile5 rewriteclaustac_key cl_rewrite_clause_tac *)

let general_s_rewrite cl l2r occs (c,l) ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo, strat = apply_lemma gl (c,l) cl l2r occs in
    try
      tclWEAK_PROGRESS 
	(tclTHEN
           (Refiner.tclEVARS (Evd.merge (project gl) hypinfo.cl.evd))
	   (cl_rewrite_clause_tac hypinfo.abs strat (mkMeta meta) cl)) gl
    with RewriteFailure e ->
      let {l2r=l2r; c1=x; c2=y} = hypinfo in
	raise (Pretype_errors.PretypeError
		  (pf_env gl,project gl,
		  Pretype_errors.NoOccurrenceFound ((if l2r then x else y), cl)))

let general_s_rewrite_clause x =
  init_setoid ();
  match x with
    | None -> general_s_rewrite None
    | Some id -> general_s_rewrite (Some id)

let _ = Hook.set Equality.general_rewrite_clause general_s_rewrite_clause

(** [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let not_declared env ty rel =
  tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared " ++
		str ty ++ str" relation. Maybe you need to require the Setoid library")

let setoid_proof gl ty fn fallback =
  let env = pf_env gl in
    try
      let rel, args = decompose_app_rel env (project gl) (pf_concl gl) in
      let evm = project gl in
      let car = pi3 (List.hd (fst (Reduction.dest_prod env (Typing.type_of env evm rel)))) in
	fn env evm car rel gl
    with e when Errors.noncritical e ->
      try fallback gl
      with Hipattern.NoEquationFound ->
          let e = Errors.push e in
	  match e with
	  | Not_found ->
	      let rel, args = decompose_app_rel env (project gl) (pf_concl gl) in
		not_declared env ty rel gl
	  | _ -> raise e

let tac_open ((evm,_), c) tac = 
  tclTHEN (Refiner.tclEVARS evm) (tac c)

let poly_proof getp gett env evm car rel =
  if Sorts.is_prop (sort_of_rel env evm rel) then
    getp env (evm,Evar.Set.empty) car rel
  else gett env (evm,Evar.Set.empty) car rel

let setoid_reflexivity gl =
  setoid_proof gl "reflexive"
    (fun env evm car rel -> 
      tac_open (poly_proof PropGlobal.get_reflexive_proof TypeGlobal.get_reflexive_proof
		  env evm car rel) apply)
    (reflexivity_red true)

let setoid_symmetry gl =
  setoid_proof gl "symmetric"
    (fun env evm car rel -> 
      tac_open (poly_proof PropGlobal.get_symmetric_proof TypeGlobal.get_symmetric_proof
		  env evm car rel) apply)
    (symmetry_red true)

let setoid_transitivity c gl =
  setoid_proof gl "transitive"
    (fun env evm car rel ->
      let proof = poly_proof PropGlobal.get_transitive_proof TypeGlobal.get_transitive_proof
	env evm car rel in
	match c with
	| None -> tac_open proof eapply
	| Some c -> tac_open proof (fun t -> apply_with_bindings (t,ImplicitBindings [ c ])))
    (transitivity_red true c)
    
let setoid_symmetry_in id gl =
  let ctype = pf_type_of gl (mkVar id) in
  let binders,concl = decompose_prod_assum ctype in
  let (equiv, args) = decompose_app concl in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z -> let l,res = split_last_two (y::z) in x::l, res
    | _ -> error "The term provided is not an equivalence."
  in
  let others,(c1,c2) = split_last_two args in
  let he,c1,c2 =  mkApp (equiv, Array.of_list others),c1,c2 in
  let new_hyp' =  mkApp (he, [| c2 ; c1 |]) in
  let new_hyp = it_mkProd_or_LetIn new_hyp'  binders in
    tclTHENS (Tactics.cut new_hyp)
      [ intro_replacing id;
	tclTHENLIST [ intros; setoid_symmetry; apply (mkVar id); Tactics.assumption ] ]
      gl

let _ = Hook.set Tactics.setoid_reflexivity setoid_reflexivity
let _ = Hook.set Tactics.setoid_symmetry setoid_symmetry
let _ = Hook.set Tactics.setoid_symmetry_in setoid_symmetry_in
let _ = Hook.set Tactics.setoid_transitivity setoid_transitivity

let implify id gl =
  let (_, b, ctype) = pf_get_hyp gl id in
  let binders,concl = decompose_prod_assum ctype in
  let evm, ctype' =
    match binders with
    | (_, None, ty as hd) :: tl when noccurn 1 concl ->
	let env = Environ.push_rel_context tl (pf_env gl) in
	let sigma = project gl in
	let tyhd = Typing.type_of env sigma ty
	and tyconcl = Typing.type_of (Environ.push_rel hd env) sigma concl in
	let ((sigma,_), app), unfold = 
	  PropGlobal.arrow_morphism (sigma, Evar.Set.empty) tyhd 
	    (subst1 mkProp tyconcl) ty (subst1 mkProp concl) 
	in
	  sigma, it_mkProd_or_LetIn app tl
    | _ -> project gl, ctype
  in tclTHEN (Refiner.tclEVARS evm) (Tacmach.convert_hyp (id, b, ctype')) gl

let rec fold_matches env sigma c =
  map_constr_with_full_binders Environ.push_rel 
    (fun env c ->
      match kind_of_term c with
      | Case _ ->
          let cst, env, c', _eff = fold_match ~force:true env sigma c in
	    fold_matches env sigma c'
      | _ -> fold_matches env sigma c)
    env c

let fold_match_tac c gl =
  let _, _, c', eff = fold_match ~force:true (pf_env gl) (project gl) c in
  let gl = { gl with sigma = Evd.emit_side_effects eff gl.sigma } in
    change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl gl

let fold_matches_tac c gl =
  let c' = fold_matches (pf_env gl) (project gl) c in
  (* let gl = { gl with sigma = Evd.emit_side_effects eff gl.sigma } in *)
    change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl gl

let myapply id l gl =
  let gr = id in
  let _, impls = List.hd (Impargs.implicits_of_global gr) in
  let env = pf_env gl in
  let evars = ref (project gl) in
  let evd, ty = fresh_global env !evars gr in
  let _ = evars := evd in
  let app =
    let rec aux ty impls args args' =
      match impls, kind_of_term ty with
      | Some (_, _, (_, _)) :: impls, Prod (n, t, t') ->
	let arg = Evarutil.e_new_evar evars env t in
	  aux (subst1 arg t') impls args (arg :: args')
      | None :: impls, Prod (n, t, t') ->
	(match args with
	| [] ->
	  if dependent (mkRel 1) t' then
	    let arg = Evarutil.e_new_evar evars env t in
	      aux (subst1 arg t') impls args (arg :: args')
	  else
	    let arg = Evarutil.mk_new_meta () in
	      evars := meta_declare (destMeta arg) t !evars;
	      aux (subst1 arg t') impls args (arg :: args')
	| arg :: args -> 
	  aux (subst1 arg t') impls args (arg :: args'))
      | _, _ -> mkApp (Universes.constr_of_global gr, Array.of_list (List.rev args'))
    in aux ty impls l []
  in
    tclTHEN (Refiner.tclEVARS !evars) (apply app) gl

let get_lemma_proof f env evm x y = 
  let (evm, _), c = f env (evm,Evar.Set.empty) x y in
    evm, c

let get_reflexive_proof =
  get_lemma_proof PropGlobal.get_reflexive_proof

let get_symmetric_proof = 
  get_lemma_proof PropGlobal.get_symmetric_proof

let get_transitive_proof = 
  get_lemma_proof PropGlobal.get_transitive_proof
  
