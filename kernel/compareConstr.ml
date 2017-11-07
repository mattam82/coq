(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constr
open Univ
open Names
open CErrors

type conv_pb = CONV | CUMUL

let get_cumulativity_constraints cv_pb cumi u u' =
  let length_ind_instance =
    Univ.AUContext.size (Univ.ACumulativityInfo.univ_context cumi)
  in
  let ind_subtypctx = Univ.ACumulativityInfo.subtyp_context cumi in
  if not ((length_ind_instance = Univ.Instance.length u) &&
          (length_ind_instance = Univ.Instance.length u')) then
     anomaly (Pp.str "Invalid inductive subtyping encountered!")
  else
    let comp_cst =
      let comp_subst = (Univ.Instance.append u u') in
      Univ.AUContext.instantiate comp_subst ind_subtypctx
    in
    match cv_pb with
    | CONV ->
      let comp_cst' =
        let comp_subst = (Univ.Instance.append u' u) in
        Univ.AUContext.instantiate comp_subst ind_subtypctx
      in
      Univ.Constraint.union comp_cst comp_cst'
    | CUMUL -> comp_cst

let convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,ind) nargs u1 u2 s =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    assert (Univ.Instance.length u1 = 0 && Univ.Instance.length u2 = 0);
    s
  | Declarations.Polymorphic_ind _ ->
    cmp_instances u1 u2 s
  | Declarations.Cumulative_ind cumi ->
    let num_param_arity =
      mind.Declarations.mind_nparams +
      mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs
    in
    if not (Int.equal num_param_arity nargs) then
      cmp_instances u1 u2 s
    else
      let csts = get_cumulativity_constraints cv_pb cumi u1 u2 in
      cmp_cumul csts s

let convert_constructors_gen cmp_instances cmp_cumul (mind, ind, cns) nargs u1 u2 s =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    assert (Univ.Instance.length u1 = 0 && Univ.Instance.length u2 = 0);
    s
  | Declarations.Polymorphic_ind _ ->
    cmp_instances u1 u2 s
  | Declarations.Cumulative_ind cumi ->
    let num_cnstr_args =
      let nparamsctxt =
        mind.Declarations.mind_nparams +
        mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs
        (* Context.Rel.length mind.Declarations.mind_params_ctxt *) in
      nparamsctxt + mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(cns - 1)
    in
    if not (Int.equal num_cnstr_args nargs) then
      cmp_instances u1 u2 s
    else
      let csts = get_cumulativity_constraints CONV cumi u1 u2 in
      cmp_cumul csts s

(* When using compare_head_gen_with we need to return a bool.
   The argument [s] passed to convert_foo_gen is the value for the monomorphic case, ie true.
 *)
let check_globref_univs env univs cv_pb ref nargs u u' =
  let cmp_instances u u' _ = UGraph.check_eq_instances univs u u' in
  let cmp_cumul csts _ = UGraph.check_constraints csts univs in
  match ref with
  | VarRef _ -> assert false
  | ConstRef _ ->
    UGraph.check_eq_instances univs u u'
  | IndRef ind ->
    let mind = Environ.lookup_mind (fst ind) env in
    convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,snd ind) nargs u u' true
  | ConstructRef ((mi,ind),ctor) ->
    let mind = Environ.lookup_mind mi env in
    convert_constructors_gen cmp_instances cmp_cumul (mind, ind, ctor) nargs u u' true

let infer_globref_univs env univs cv_pb cstsref ref nargs u u' =
  let cmp_instances u u' _ =
    if UGraph.check_eq_instances univs u u' then true
    else begin cstsref := enforce_eq_instances u u' !cstsref; true end
  in
  let cmp_cumul csts _ =
    if UGraph.check_constraints csts univs then true
    else begin cstsref := Constraint.union csts !cstsref; true end
  in
  match ref with
  | VarRef _ -> assert false
  | ConstRef _ ->
    (* If this check fails we don't add constraints as reducing could
       give a better result. *)
    UGraph.check_eq_instances univs u u'
  | IndRef ind ->
    let mind = Environ.lookup_mind (fst ind) env in
    convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,snd ind) nargs u u' true
  | ConstructRef ((mi,ind),ctor) ->
    let mind = Environ.lookup_mind mi env in
    convert_constructors_gen cmp_instances cmp_cumul (mind, ind, ctor) nargs u u' true

let eq_constr_univs env univs m n =
  if m == n then true
  else
    let eq_universes = check_globref_univs env univs CONV in
    let eq_sorts s1 s2 =
      s1 == s2 ||
      UGraph.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2)
    in
    let rec eq_constr' m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' m n
    in compare_head_gen eq_universes eq_sorts eq_constr' m n

let leq_constr_univs env univs m n =
  if m == n then true
  else
    let eq_universes = check_globref_univs env univs CONV in
    let leq_universes = check_globref_univs env univs CUMUL in
    let eq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_eq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let leq_sorts s1 s2 = s1 == s2 ||
      UGraph.check_leq univs (Sorts.univ_of_sort s1) (Sorts.univ_of_sort s2) in
    let rec eq_constr' m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      compare_head_gen_leq leq_universes leq_sorts eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
    compare_leq m n

let eq_constr_univs_infer env univs m n =
  if m == n then Some Constraint.empty
  else
    let cstrs = ref Constraint.empty in
    let eq_universes = infer_globref_univs env univs CONV cstrs in
    let eq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_eq univs u1 u2 then true
        else
          (cstrs := Univ.enforce_eq u1 u2 !cstrs;
           true)
    in
    let rec eq_constr' m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let res = compare_head_gen eq_universes eq_sorts eq_constr' m n in
    if res then Some !cstrs else None

let leq_constr_univs_infer env univs m n =
  if m == n then Some Constraint.empty
  else
    let cstrs = ref Constraint.empty in
    let eq_universes = infer_globref_univs env univs CONV cstrs in
    let leq_universes = infer_globref_univs env univs CUMUL cstrs in
    let eq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_eq univs u1 u2 then true
        else (cstrs := Univ.enforce_eq u1 u2 !cstrs;
              true)
    in
    let leq_sorts s1 s2 =
      if Sorts.equal s1 s2 then true
      else
        let u1 = Sorts.univ_of_sort s1 and u2 = Sorts.univ_of_sort s2 in
        if UGraph.check_leq univs u1 u2 then true
        else
          (cstrs := Univ.enforce_leq u1 u2 !cstrs;
           true)
    in
    let rec eq_constr' m n =
      m == n || compare_head_gen eq_universes eq_sorts eq_constr' m n
    in
    let rec compare_leq m n =
      compare_head_gen_leq leq_universes leq_sorts eq_constr' leq_constr' m n
    and leq_constr' m n = m == n || compare_leq m n in
    let res = compare_leq m n in
    if res then Some !cstrs else None
