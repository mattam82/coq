(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Entries
open Environ
open Evd
open Refiner

let refining = Proof_global.there_are_pending_proofs
let check_no_pending_proofs = Proof_global.check_no_pending_proof

let get_current_proof_name = Proof_global.get_current_proof_name
let get_all_proof_names = Proof_global.get_all_proof_names

type lemma_possible_guards = Proof_global.lemma_possible_guards

let delete_proof = Proof_global.discard
let delete_current_proof = Proof_global.discard_current
let delete_all_proofs = Proof_global.discard_all

let set_undo _ = ()
let get_undo _ = None

let start_proof (id : Id.t) str hyps c ?init_tac ?compute_guard hook =
  let goals = [ (Global.env_of_context hyps , c) ] in
  Proof_global.start_proof id str goals ?compute_guard hook;
  let env = Global.env () in
  Proof_global.with_current_proof (fun _ p ->
    match init_tac with
    | None -> p
    | Some tac -> Proof.run_tactic env (Proofview.V82.tactic tac) p)

let cook_this_proof hook p =
  match p with
  | (i,([e],cstrs,cg,str,h)) -> (i,(e,cstrs,cg,str,h))
  | _ -> Errors.anomaly ~label:"Pfedit.cook_proof" (Pp.str "more than one proof term.")

let cook_proof hook = cook_this_proof hook (Proof_global.close_proof ())
let get_pftreestate () =
  Proof_global.give_me_the_proof ()

let set_end_tac tac =
  Proof_global.set_endline_tactic tac

let set_used_variables l =
  Proof_global.set_used_variables l
let get_used_variables () =
  Proof_global.get_used_variables ()

exception NoSuchGoal
let _ = Errors.register_handler begin function
  | NoSuchGoal -> Errors.error "No such goal."
  | _ -> raise Errors.Unhandled
end
let get_nth_V82_goal i =
  let p = Proof_global.give_me_the_proof () in
  let { it=goals ; sigma = sigma; } = Proof.V82.subgoals p in
  try
          { it=(List.nth goals (i-1)) ; sigma=sigma; }
  with Failure _ -> raise NoSuchGoal
    
let get_goal_context_gen i =
  try
let { it=goal ; sigma=sigma; } =  get_nth_V82_goal i in
(sigma, Refiner.pf_env { it=goal ; sigma=sigma; })
  with Proof_global.NoCurrentProof -> Errors.error "No focused proof."

let get_goal_context i =
  try get_goal_context_gen i
  with NoSuchGoal -> Errors.error "No such goal."

let get_current_goal_context () =
  try get_goal_context_gen 1
  with NoSuchGoal ->
    (* spiwack: returning empty evar_map, since if there is no goal, under focus,
        there is no accessible evar either *)
    (Evd.empty, Global.env ())

let current_proof_statement () =
  match Proof_global.V82.get_current_initial_conclusions () with
    | (id,([concl],strength,hook)) -> id,strength,concl,hook
    | _ -> Errors.anomaly ~label:"Pfedit.current_proof_statement" (Pp.str "more than one statement")

let solve_nth ?with_end_tac gi tac pr =
  try 
    let tac = Proofview.V82.tactic tac in
    let tac = match with_end_tac with
      | None -> tac
      | Some etac -> Proofview.tclTHEN tac etac in
    Proof.run_tactic (Global.env ()) (Proofview.tclFOCUS gi gi tac) pr
  with
    | Proof_global.NoCurrentProof  -> Errors.error "No focused proof"
    | Proofview.IndexOutOfRange ->
	let msg = str "No such goal: " ++ int gi ++ str "." in
	Errors.errorlabstrm "" msg

let by tac = Proof_global.with_current_proof (fun _ -> solve_nth 1 tac)

let instantiate_nth_evar_com n com = 
  Proof_global.with_current_proof (fun _ -> Proof.V82.instantiate_evar n com)


(**********************************************************************)
(* Shortcut to build a term using tactics *)

open Decl_kinds

let next = let n = ref 0 in fun () -> incr n; !n

let build_constant_by_tactic id sign ?(goal_kind = Global, false, Proof Theorem) typ tac =
  let substref = ref Univ.LMap.empty in
    start_proof id goal_kind sign typ (Some (fun subst -> substref := fst subst; fun _ _ -> ()));
    try
      by tac;
      let _,(const,_,_,_,h) = cook_proof (fun _ -> ()) in
	delete_current_proof ();
	const, !substref
    with reraise ->
      delete_current_proof ();
      raise reraise

let constr_of_def = function
  | Declarations.Undef _ -> assert false
  | Declarations.Def cs -> Lazyconstr.force cs
  | Declarations.OpaqueDef lc -> Lazyconstr.force_opaque (Future.force lc)

let build_by_tactic env ?(poly=false) typ tac =
  let id = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = val_of_named_context (named_context env) in
  let gk = Global, poly, Proof Theorem in
  let ce, subst = build_constant_by_tactic id sign ~goal_kind:gk typ tac in
  let ce = Term_typing.handle_side_effects env ce in
  let cb, se = Future.force ce.const_entry_body in
  assert(Declareops.side_effects_is_empty se);
  cb, subst

(**********************************************************************)
(* Support for resolution of evars in tactic interpretation, including
   resolution by application of tactics *)

let implicit_tactic = ref None

let declare_implicit_tactic tac = implicit_tactic := Some tac

let solve_by_implicit_tactic env sigma evk =
  let evi = Evd.find_undefined sigma evk in
  match (!implicit_tactic, snd (evar_source evk sigma)) with
  | Some tac, (Evar_kinds.ImplicitArg _ | Evar_kinds.QuestionMark _)
      when
	Context.named_context_equal (Environ.named_context_of_val evi.evar_hyps)
	(Environ.named_context env) ->
      (try fst (build_by_tactic env (evi.evar_concl, Evd.get_universe_context_set sigma)
	   (tclCOMPLETE tac))
       with e when Logic.catchable_exception e -> raise Exit)
  | _ -> raise Exit
