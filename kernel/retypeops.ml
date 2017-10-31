(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open Constr
open Vars
open Declarations
open Environ
open Type_errors

module RelDecl = Context.Rel.Declaration

module WhdEvars = struct
  open CClosure

  let whd_all env evars t =
    match kind t with
    | (Sort _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | App (c, _) ->
      begin match kind c with
        | Ind _ | Construct _ -> t
        | _ -> whd_val (create_clos_infos ~evars all env) (inject t)
      end
    | _ -> whd_val (create_clos_infos ~evars all env) (inject t)

  let whd_allnolet env evars t =
    match kind t with
    | (Sort _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | App (c, _) ->
      begin match kind c with
        | Ind _ | Construct _| LetIn _ -> t
        | _ -> whd_val (create_clos_infos allnolet env) (inject t)
      end
    | _ -> whd_val (create_clos_infos allnolet env) (inject t)

  let dest_prod_assum env evars =
    let open Context.Rel.Declaration in
    let rec prodec_rec env l ty =
      let rty = whd_allnolet env evars ty in
      match kind rty with
      | Prod (x,t,c)  ->
        let d = LocalAssum (x,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
      | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
      | Cast (c,_,_)    -> prodec_rec env l c
      | _               ->
        let rty' = whd_all env evars rty in
        if Constr.equal rty' rty then l, rty
        else prodec_rec env l rty'
    in
    prodec_rec env Context.Rel.empty

  let dest_arity env evars c =
  let l, c = dest_prod_assum env evars c in
  match kind c with
    | Sort s -> l,s
    | _ -> raise NotArity

end
open WhdEvars

module Ind = struct
  (* Some helpers for inductive types. *)
  (* raise Not_found if not an inductive type *)
  let lookup_mind_specif env (kn,tyi) =
    let mib = Environ.lookup_mind kn env in
    if tyi >= Array.length mib.mind_packets then
      user_err Pp.(str "Ind.lookup_mind_specif: invalid inductive index");
    (mib, mib.mind_packets.(tyi))

  let find_rectype env evars c =
    let (t, l) = Term.decompose_app (whd_all env evars c) in
    match kind t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

  let inductive_params (mib,_) = mib.mind_nparams

  (* Template polymorphism *)

  (* cons_subst add the mapping [u |-> su] in subst if [u] is not *)
  (* in the domain or add [u |-> sup x su] if [u] is already mapped *)
  (* to [x]. *)
  let cons_subst u su subst =
    try
      Univ.LMap.add u (Univ.sup (Univ.LMap.find u subst) su) subst
    with Not_found -> Univ.LMap.add u su subst

  (* remember_subst updates the mapping [u |-> x] by [u |-> sup x u] *)
  (* if it is presents and returns the substitution unchanged if not.*)
  let remember_subst u subst =
    try
      let su = Universe.make u in
      Univ.LMap.add u (Univ.sup (Univ.LMap.find u subst) su) subst
    with Not_found -> subst

  (* Bind expected levels of parameters to actual levels *)
  (* Propagate the new levels in the signature *)
  let make_subst env evars =
    let open RelDecl in
    let rec make subst = function
      | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
      | d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
      | d::sign, Some u::exp, a::args ->
        (* We recover the level of the argument, but we don't change the *)
        (* level in the corresponding type in the arity; this level in the *)
        (* arity is a global level which, at typing time, will be enforce *)
        (* to be greater than the level of the argument; this is probably *)
        (* a useless extra constraint *)
        let s = Sorts.univ_of_sort (snd (dest_arity env evars (Lazy.force a))) in
        make (cons_subst u s subst) (sign, exp, args)
      | LocalAssum (na,t) :: sign, Some u::exp, [] ->
        (* No more argument here: we add the remaining universes to the *)
        (* substitution (when [u] is distinct from all other universes in the *)
        (* template, it is identity substitution  otherwise (ie. when u is *)
        (* already in the domain of the substitution) [remember_subst] will *)
        (* update its image [x] by [sup x u] in order not to forget the *)
        (* dependency in [u] that remains to be fullfilled. *)
        make (remember_subst u subst) (sign, exp, [])
      | sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
      | [], _, _ ->
        assert false
    in
    make Univ.LMap.empty

  let instantiate_universes env evars ctx ar argsorts =
    let args = Array.to_list argsorts in
    let subst = make_subst env evars (ctx,ar.template_param_levels,args) in
    let level = Univ.subst_univs_universe (Univ.make_subst subst) ar.template_level in
    let ty = Sorts.sort_of_univ level in
    (ctx, ty)

  (* [p] is the predicate, [c] is the match object, [realargs] is the
     list of real args of the inductive type *)
  let build_case_type env n p c realargs =
    (* Don't care about evars here? *)
    CClosure.whd_betaiota env (Term.lambda_appvect_assum (n+1) p (Array.of_list (realargs@[c])))

  let type_of_case env (pind,largs) p c =
    let specif = lookup_mind_specif env (fst pind) in
    let nparams = inductive_params specif in
    let (params,realargs) = List.chop nparams largs in
    let ty = build_case_type env (snd specif).mind_nrealdecls p c realargs in
    ty

  (* Build the substitution that replaces Rels by the appropriate
     inductives *)
  let ind_subst mind mib u =
    let ntypes = mib.mind_ntypes in
    let make_Ik k = mkIndU ((mind,ntypes-k-1),u) in
    List.init ntypes make_Ik

  let constructor_instantiate mind u mib c =
    let s = ind_subst mind mib u in
    substl s (subst_instance_constr u c)

  let type_of_constructor (cstr, u) (mib,mip) =
    let ind = inductive_of_constructor cstr in
    let specif = mip.mind_user_lc in
    let i = index_of_constructor cstr in
    let nconstr = Array.length mip.mind_consnames in
    if i > nconstr then user_err Pp.(str "Not enough constructors in the type.");
    constructor_instantiate (fst ind) u mib specif.(i-1)

  let type_of_inductive_gen env evars ((mib,mip),u) paramtyps =
    match mip.mind_arity with
    | RegularArity a -> subst_instance_constr u a.mind_user_arity
    | TemplateArity ar ->
      let ctx = List.rev mip.mind_arity_ctxt in
      let ctx,s = instantiate_universes env evars ctx ar paramtyps in
      Term.mkArity (List.rev ctx,s)

  let type_of_inductive env evars pind =
    type_of_inductive_gen env evars pind [||]

  let type_of_inductive_knowing_parameters env evars mip args =
    type_of_inductive_gen env evars mip args
end

(* This should be a type (a priori without intention to be an assumption) *)
let check_type env evars c t =
  match kind(whd_all env evars t) with
  | Sort s -> s
  | _ -> error_not_type env (make_judge c t)

let dest_sort_opt env evars t =
  match kind (whd_all env evars t) with
  | Sort s -> Some s
  | _ -> None

(************************************************)
(* Incremental typing rules: builds a typing judgment given the *)
(* judgments for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let type_of_prop = mkSort Sorts.type1

(* Type of Type(i). *)

let type_of_type u =
  let uu = Sorts.super u in
    mkSort uu

(*s Type of a de Bruijn index. *)

let type_of_relative env n =
  try
    env |> lookup_rel n |> RelDecl.get_type |> lift n
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let type_of_variable env id =
  try named_type id env
  with Not_found ->
    error_unbound_var env id

(* Type of constants *)

let type_of_constant env cst =
  constant_type_in env cst

(* Type of a lambda-abstraction. *)

(* [type_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let type_of_abstraction env name var ty =
  mkProd (name, var, ty)

(* Type of an application. *)

let make_judgev c t = 
  Array.map2 make_judge c t

let type_of_apply env evars func funt argsv argstv =
  let len = Array.length argsv in
  let rec apply_rec i typ = 
    if Int.equal i len then typ
    else 
      (match kind (whd_all env evars typ) with
      | Prod (_,c1,c2) ->
	let arg = argsv.(i) in
	apply_rec (i+1) (subst1 arg c2)
      | _ ->
	error_cant_apply_not_functional env 
	  (make_judge func funt)
	  (make_judgev argsv (Array.map Lazy.force argstv)))
  in apply_rec 0 funt

(* Type of product *)

let is_impredicative_sort env s =
  let open Sorts in
  match s with
  | SProp | Prop -> true
  | Set -> is_impredicative_set env
  | _ -> false

let sort_of_product env domsort rangsort =
  let open Sorts in
  match (domsort, rangsort) with
    | (_, SProp) | (SProp, _) -> rangsort
    (* Product rule (s,Prop,Prop) *)
    | (_,       Prop)  -> rangsort
    (* Product rule (Prop/Set,Set,Set) *)
    | ((Prop | Set),  Set) -> rangsort
    (* Product rule (Type,Set,?) *)
    | (Type u1, Set) ->
        if is_impredicative_set env then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Sorts.sort_of_univ (Universe.sup Universe.type0 u1)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Set,  Type u2)  -> Sorts.sort_of_univ (Universe.sup Universe.type0 u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Sorts.sort_of_univ (Universe.sup u1 u2)

(* [type_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)
let type_of_product env name s1 s2 =
  let s = sort_of_product env s1 s2 in
    mkSort s

(* Inductive types. *)

(* The type is parametric over the uniform parameters whose conclusion
   is in Type; to enforce the internal constraints between the
   parameters and the instances of Type occurring in the type of the
   constructors, we use the level variables _statically_ assigned to
   the conclusions of the parameters as mediators: e.g. if a parameter
   has conclusion Type(alpha), static constraints of the form alpha<=v
   exist between alpha and the Type's occurring in the constructor
   types; when the parameters is finally instantiated by a term of
   conclusion Type(u), then the constraints u<=alpha is computed in
   the App case of execute; from this constraints, the expected
   dynamic constraints of the form u<=v are enforced *)

let type_of_inductive_knowing_parameters env evars (ind,u) args =
  let spec = Ind.lookup_mind_specif env ind in
  Ind.type_of_inductive_knowing_parameters env evars (spec,u) args

let type_of_inductive env evars (ind,u) =
  let spec = Ind.lookup_mind_specif env ind in
  Ind.type_of_inductive env evars (spec,u)

(* Constructors. *)

let type_of_constructor env (c,u as cu) =
  let specif = Ind.lookup_mind_specif env (inductive_of_constructor c) in
  Ind.type_of_constructor cu specif

(* Case. *)

let type_of_case env evars p c ct =
  let (pind, _ as indspec) =
    try Ind.find_rectype env evars ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  Ind.type_of_case env indspec p c

let type_of_projection env evars p c ct =
  let pb = lookup_projection p env in
  let (ind,u), args =
    try Ind.find_rectype env evars ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(MutInd.equal pb.proj_ind (fst ind));
  let ty = Vars.subst_instance_constr u pb.Declarations.proj_type in
  substl (c :: List.rev args) ty

(************************************************************************)
(************************************************************************)

(* The typing machine. *)
let rec infer env evars cstr =
  let open Context.Rel.Declaration in
  match kind cstr with
  (* Atomic terms *)
  | Sort s when Sorts.is_small s ->
    type_of_prop

  | Sort u ->
    type_of_type u

  | Rel n ->
    type_of_relative env n

  | Var id ->
    type_of_variable env id

  | Const c ->
    type_of_constant env c

  | Proj (p, c) ->
    let ct = infer env evars c in
    type_of_projection env evars p c ct

  (* Lambda calculus operators *)
  | App (f,args) ->
    let argst = Array.map (fun c -> lazy (infer env evars c)) args in
    let ft =
      match kind f with
      | Ind ind when Environ.template_polymorphic_pind ind env ->
        (* Template sort-polymorphism of inductive types *)
        type_of_inductive_knowing_parameters env evars ind argst
      | _ ->
        (* Full or no sort-polymorphism *)
        infer env evars f
    in
    type_of_apply env evars f ft args argst

  | Lambda (name,c1,c2) ->
    let env1 = push_rel (LocalAssum (name,c1)) env in
    let c2t = infer env1 evars c2 in
    type_of_abstraction env name c1 c2t

  | Prod (name,c1,c2) ->
    let env1 = push_rel (LocalAssum (name,c1)) env in
    let rang = infer_type env1 evars c2 in
    if is_impredicative_sort env rang then mkSort rang
    else
      let dom = infer_type env evars c1 in
      type_of_product env name dom rang

  | LetIn (name,c1,c2,c3) ->
    let env1 = push_rel (LocalDef (name,c1,c2)) env in
    let c3t = infer env1 evars c3 in
    subst1 c1 c3t

  | Cast (c,k,t) -> t

  (* Inductive types *)
  | Ind ind ->
    type_of_inductive env evars ind

  | Construct c ->
    type_of_constructor env c

  | Case (ci,p,c,lf) ->
    let ct = infer env evars c in
    type_of_case env evars p c ct

  | Fix ((vn,i),(_,lar,_)) ->
    lar.(i)

  | CoFix (i,(_,lar,_)) ->
    lar.(i)

  (* Partial proofs: unsupported by the kernel *)
  | Meta m ->
    evars.meta_type m

  | Evar ev ->
    evars.evar_type ev

and infer_type env evars constr =
  let t = infer env evars constr in
  check_type env evars constr t

(* TODO maybe can skip some constructions *)
let is_irrelevant_type env evars t =
  let open Sorts in
  let sconstr = infer env evars t in
  match dest_sort_opt env evars sconstr with
  | None -> false (* not a type *)
  | Some (Prop | Set | Type _) -> false (* relevant type *)
  | Some SProp -> true

let rec is_irrelevant_term env evars constr =
  let open RelDecl in
  match kind constr with
  | Sort _ | Prod _ -> false (* types are always relevant *)

  | Lambda (na, t, b) -> (* impredicativity of SProp *)
    let env = push_rel (LocalAssum (na, t)) env in
    is_irrelevant_term env evars b

  | LetIn (na,v,t,b) ->
    let env = push_rel (LocalDef (na,v,t)) env in
    is_irrelevant_term env evars b

  | App (f,_) ->
    (* This is the main gain of non cumulative SProp (until we mark
       terms as we build them).

       Obviously if ⊢ f : Π x, B : SProp then x ⊢ B : SProp and ⊢
       B[args] : SProp

       If ⊢ f a : T : SProp then T ≡ B[a] for some B, then ⊢ f : Π x,
       B : s

       With cumulativity we can have [B x := (if x then True else
       Unit) : Set] and [a := true], then [B a ≡ True : SProp].

       Without cumulativity we get B[a] : s related to SProp which
       implies s ≡ SProp.

       TODO check this principle that if a term has 2 types they are related.
    *)
    is_irrelevant_term env evars f

  (* Default case: look at the type. *)
  | Rel _ | Var _ | Const _ | Ind _ | Construct _
  | Case _ | Fix _ | CoFix _ | Proj _
  | Meta _ | Evar _
  | Cast _ (* Cast: maybe look inside instead? *) ->
    let t = infer env evars constr in
    is_irrelevant_type env evars t
