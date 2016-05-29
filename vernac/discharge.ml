(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open CErrors
open Util
open Term
open Vars
open Declarations
open Cooking
open Entries
open Context.Rel.Declaration

(********************************)
(* Discharging mutual inductive *)

let detype_param =
  function
  | LocalAssum (Name id, p) -> id, LocalAssumEntry p
  | LocalDef (Name id, p,_) -> id, LocalDefEntry p
  | _ -> anomaly (Pp.str "Unnamed inductive local variable")

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let find_index mcons i j l =
  (* nbc before the current inductive - nbc for the referenced inductive
    = constructors between the current inductive and the referenced one *)
  (mcons.(i) - mcons.(j)) - (l - 1)
      
let abstract_constructors mind mcons nparams i cur c =
  let rec aux k c =
    let c', app = decompose_appvect c in
    match kind_of_term c' with
    | Construct (((ind, j), l), u) when eq_mind mind ind ->
       let f =
         if Int.equal j i then mkRel (k + (cur + 1) - l)
         else mkRel (k + cur + find_index mcons i j l)
       in mkApp (f, Array.map (aux k)
                           (Array.sub app nparams (Array.length app - nparams)))
    | Rel n ->
       if n <= k then mkApp (c', Array.map (aux k) app)
       else mkApp (mkRel (n + cur + mcons.(i)), Array.map (aux k) app)
    | _ -> map_constr_with_binders succ aux k c
  in aux 0 c

let abstract_inductives mind nparams' i c =
  let rec aux k c =
    match kind_of_term c with
    | Ind ((ind, j), u) when eq_mind mind ind -> mkRel (k + (i - j))
    | Rel n -> if n <= k then c else mkRel (n + i)
    | _ -> map_constr_with_binders succ aux k c
  in aux nparams' c

let mkNamedProd_wo_LetIn decl k c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) ->  mkProd (Name id, t, substn_vars (k + 1) [id] c)
    | LocalDef (id,b,t) -> substnl [b] k (substn_vars (k+1) [id] c)

let it_mkNamedProd_wo_LetIn k b hyps =
  List.fold_left (fun c d -> mkNamedProd_wo_LetIn d k c) b hyps
                                  
let abstract_inductive mind hyps nparams constrs inds =
  let mind' = Globnames.pop_kn mind in
  let ntyp = Array.length inds in
  let nhyp = Context.Named.length hyps in
  let args = Context.Named.to_instance mkVar (List.rev hyps) in
  let args = Array.of_list args in
  let subs = List.init ntyp (fun k -> lift nhyp (mkApp(mkRel (k+1),args))) in
  let nparams' = nparams + Array.length args in
  let inds' =
    Array.mapi
      (fun i (tname,arity,template,cnames,lc) ->
        let liftk = constrs.(i) in
        let lc' = List.mapi (fun j c ->
                      let ctx, c = decompose_prod_n_assum nparams c in
                      let c = abstract_constructors mind' constrs nparams' i j c in
                      (** hyps ; I1..In, params, c0..cliftk, ci0..cij |- c,
                          I1..In, hyps |- subs : I1..In *)
                      substnl subs (liftk + j + nparams) c) lc in
	let lc'' =
          List.mapi (fun j b ->
              let prodpars' = it_mkNamedProd_wo_LetIn (liftk + j + nparams) b hyps in
              snd (decompose_prod_n_assum (Array.length args) prodpars')) lc' in
	let arity = it_mkNamedProd_wo_LetIn 0 arity hyps in
        let params, arity = decompose_prod_n_assum nparams' arity in
        let arity = abstract_inductives mind' nparams' i arity in
        (tname,params,arity,template,cnames,lc''))
      	inds in
  (* To be sure to be the same as before, should probably be moved to process_inductive *)
  let inds' = Array.to_list inds' in
  let params' = let (_,params,arity,_,_,_) = List.hd inds' in
                List.map detype_param params
  in
  let ind'' =
  List.mapi
    (fun i (a,_,arity,template,c,lc) ->
      { mind_entry_typename = a;
	mind_entry_arity = arity;
	mind_entry_template = template;
	mind_entry_consnames = c;
	mind_entry_lc = lc })
    inds'
  in (params',ind'')

let refresh_polymorphic_type_of_inductive (_,mip) =
  match mip.mind_arity with
  | RegularArity s -> s.mind_user_arity, false
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
      mkArity (List.rev ctx, Type ar.template_level), true

let process_inductive (sechyps,abs_ctx) modlist mind mib =
  let nparams = mib.mind_nparams in
  let subst, univs = 
    if mib.mind_polymorphic then 
      let inst = Univ.UContext.instance mib.mind_universes in
      let cstrs = Univ.UContext.constraints mib.mind_universes in
	inst, Univ.UContext.make (inst, Univ.subst_instance_constraints inst cstrs)
    else Univ.Instance.empty, mib.mind_universes
  in
  let constrs =
    let init = Array.map (fun mip -> Array.length mip.mind_user_lc) mib.mind_packets in
    let init = Array.cons 0 init in
    for i = 1 to Array.length init - 1 do
      init.(i) <- init.(i-1) + init.(i)
    done;
    init
  in
  let inds =
    Array.map
      (fun mip ->
	let ty, template = refresh_polymorphic_type_of_inductive (mib,mip) in
	let arity = expmod_constr modlist ty in
	let arity = Vars.subst_instance_constr subst arity in
	let lc =
          Array.map
            (fun c -> Vars.subst_instance_constr subst (expmod_constr modlist c))
	    mip.mind_user_lc
	in
	  (mip.mind_typename,
	   arity, template,
	   Array.to_list mip.mind_consnames,
	   Array.to_list lc))
      mib.mind_packets in
  let sechyps' = Context.Named.map (expmod_constr modlist) sechyps in
  let (params',inds') = abstract_inductive mind sechyps' nparams constrs inds in
  let abs_ctx = Univ.instantiate_univ_context abs_ctx in
  let univs = Univ.UContext.union abs_ctx univs in
  let record = match mib.mind_record with
    | Some (Some (id, _, _)) -> Some (Some id)
    | Some None -> Some None
    | None -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_polymorphic = mib.mind_polymorphic;
    mind_entry_private = mib.mind_private;
    mind_entry_universes = univs;
  }
