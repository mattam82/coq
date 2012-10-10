(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file builds schemes related to case analysis and recursion schemes *)

open Term
open Indrec
open Declarations
open Typeops
open Termops
open Ind_tables

(* Induction/recursion schemes *)

let optimize_non_type_induction_scheme kind dep sort ind =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if check_scheme kind ind then
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       apropriate type *)
    let sigma, cte = Evd.fresh_constant_instance env sigma (find_scheme kind ind) in
    let c = mkConstU cte in
    let t = type_of_constant_in (Global.env()) cte in
    let (mib,mip) = Global.lookup_inductive ind in
    let npars =
      (* if a constructor of [ind] contains a recursive call, the scheme
	 is generalized only wrt recursively uniform parameters *)
      if (Inductiveops.mis_is_recursive_subset [snd ind] mip.mind_recargs)
      then
	mib.mind_nparams_rec
      else
	mib.mind_nparams in
    let sigma, sort = Evd.fresh_sort_in_family env sigma sort in
    let sigma, t', c' = weaken_sort_scheme env sigma true sort npars c t in
    let sigma, nf = Evarutil.nf_evars_and_universes sigma in
      nf c, Evd.evar_universe_context sigma
  else
    let u = 
      let mib,mip = Inductive.lookup_mind_specif env ind in
	if mib.mind_polymorphic then fst mib.mind_universes 
	else [] 
    in
    let ctx = Univ.universe_context_set_of_list u in
    let sigma, c = build_induction_scheme env (Evd.from_env ~ctx env) (ind,Univ.UList.of_llist u) dep sort in
      c, Evd.evar_universe_context sigma

let build_induction_scheme_in_type dep sort ind =
  let env = Global.env () in
  let u = 
    let mib,mip = Inductive.lookup_mind_specif env ind in
      if mib.mind_polymorphic then fst mib.mind_universes 
      else [] 
  in
  let ctx = Univ.universe_context_set_of_list u in
  let sigma, c = build_induction_scheme env (Evd.from_env ~ctx env) (ind,Univ.UList.of_llist u) dep sort in
    c, Evd.evar_universe_context sigma
 
let rect_scheme_kind_from_type =
  declare_individual_scheme_object "_rect_nodep"
    (build_induction_scheme_in_type false InType)

let rect_scheme_kind_from_prop =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_prop"
    (build_induction_scheme_in_type false InType)

let rect_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_type"
    (build_induction_scheme_in_type true InType)

let ind_scheme_kind_from_type =
  declare_individual_scheme_object "_ind_nodep"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_type false InProp)

let ind_scheme_kind_from_prop =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_prop"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_prop false InProp)

let ind_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_type"
  (optimize_non_type_induction_scheme rect_dep_scheme_kind_from_type true InProp)

let rec_scheme_kind_from_prop =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_prop"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_prop false InSet)

let rec_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_type"
  (optimize_non_type_induction_scheme rect_dep_scheme_kind_from_type true InSet)

(* Case analysis *)

let build_case_analysis_scheme_in_type dep sort ind =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, indu = Evd.fresh_inductive_instance env sigma ind in
  let sigma, c = build_case_analysis_scheme env sigma indu dep sort in 
    c, Evd.evar_universe_context sigma

let case_scheme_kind_from_type =
  declare_individual_scheme_object "_case_nodep"
  (build_case_analysis_scheme_in_type false InType)

let case_scheme_kind_from_prop =
  declare_individual_scheme_object "_case" ~aux:"_case_from_prop"
  (build_case_analysis_scheme_in_type false InType)

let case_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_case" ~aux:"_case_from_type"
  (build_case_analysis_scheme_in_type true InType)

let case_dep_scheme_kind_from_type_in_prop =
  declare_individual_scheme_object "_casep_dep"
  (build_case_analysis_scheme_in_type true InProp)

let case_dep_scheme_kind_from_prop =
  declare_individual_scheme_object "_case_dep"
  (build_case_analysis_scheme_in_type true InType)

let case_dep_scheme_kind_from_prop_in_prop =
  declare_individual_scheme_object "_casep"
  (build_case_analysis_scheme_in_type true InProp)
