(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Errors
open Util
open Pcoq
open Extend
open Ppextend
open Constrexpr
open Notation_term
open Libnames
open Tacexpr
open Names
open Egramml

(**************************************************************************)
(*
 * --- Note on the mapping of grammar productions to camlp4 actions ---
 *
 * Translation of environments: a production
 *   [ nt1(x1) ... nti(xi) ] -> act(x1..xi)
 * is written (with camlp4 conventions):
 *   (fun vi -> .... (fun v1 -> act(v1 .. vi) )..)
 * where v1..vi are the values generated by non-terminals nt1..nti.
 * Since the actions are executed by substituting an environment,
 * the make_*_action family build the following closure:
 *
 *      ((fun env ->
 *          (fun vi ->
 *             (fun env -> ...
 *
 *                  (fun v1 ->
 *                     (fun env -> gram_action .. env act)
 *                     ((x1,v1)::env))
 *                  ...)
 *             ((xi,vi)::env)))
 *         [])
 *)

(**********************************************************************)
(** Declare Notations grammar rules                                   *)

let constr_expr_of_name (loc,na) = match na with
  | Anonymous -> CHole (loc,None)
  | Name id -> CRef (Ident (loc,id),None)

let cases_pattern_expr_of_name (loc,na) = match na with
  | Anonymous -> CPatAtom (loc,None)
  | Name id -> CPatAtom (loc,Some (Ident (loc,id)))

type grammar_constr_prod_item =
  | GramConstrTerminal of Tok.t
  | GramConstrNonTerminal of constr_prod_entry_key * Id.t option
  | GramConstrListMark of int * bool
    (* tells action rule to make a list of the n previous parsed items;
       concat with last parsed list if true *)

let make_constr_action
  (f : Loc.t -> constr_notation_substitution -> constr_expr) pil =
  let rec make (constrs,constrlists,binders as fullsubst) = function
  | [] ->
      Gram.action (fun (loc:CompatLoc.t) -> f (!@loc) fullsubst)
  | (GramConstrTerminal _ | GramConstrNonTerminal (_,None)) :: tl ->
      (* parse a non-binding item *)
      Gram.action (fun _ -> make fullsubst tl)
  | GramConstrNonTerminal (typ, Some _) :: tl ->
      (* parse a binding non-terminal *)
    (match typ with
    | (ETConstr _| ETOther _) ->
	Gram.action (fun (v:constr_expr) ->
	  make (v :: constrs, constrlists, binders) tl)
    | ETReference ->
        Gram.action (fun (v:reference) ->
	  make (CRef (v,None) :: constrs, constrlists, binders) tl)
    | ETName ->
        Gram.action (fun (na:Loc.t * Name.t) ->
	  make (constr_expr_of_name na :: constrs, constrlists, binders) tl)
    | ETBigint ->
        Gram.action (fun (v:Bigint.bigint) ->
	  make (CPrim(Loc.ghost,Numeral v) :: constrs, constrlists, binders) tl)
    | ETConstrList (_,n) ->
	Gram.action (fun (v:constr_expr list) ->
	  make (constrs, v::constrlists, binders) tl)
    | ETBinder _ | ETBinderList (true,_) ->
	Gram.action (fun (v:local_binder list) ->
	  make (constrs, constrlists, v::binders) tl)
    | ETBinderList (false,_) ->
	Gram.action (fun (v:local_binder list list) ->
	  make (constrs, constrlists, List.flatten v::binders) tl)
    | ETPattern ->
	failwith "Unexpected entry of type cases pattern")
  | GramConstrListMark (n,b) :: tl ->
      (* Rebuild expansions of ConstrList *)
      let heads,constrs = List.chop n constrs in
      let constrlists =
	if b then (heads@List.hd constrlists)::List.tl constrlists
	else heads::constrlists
      in make (constrs, constrlists, binders) tl
  in
  make ([],[],[]) (List.rev pil)

let check_cases_pattern_env loc (env,envlist,hasbinders) =
  if hasbinders then Topconstr.error_invalid_pattern_notation loc
  else (env,envlist)

let make_cases_pattern_action
  (f : Loc.t -> cases_pattern_notation_substitution -> cases_pattern_expr) pil =
  let rec make (env,envlist,hasbinders as fullenv) = function
  | [] ->
      Gram.action
	(fun (loc:CompatLoc.t) ->
	  let loc = !@loc in
	  f loc (check_cases_pattern_env loc fullenv))
  | (GramConstrTerminal _ | GramConstrNonTerminal (_,None)) :: tl ->
      (* parse a non-binding item *)
      Gram.action (fun _ -> make fullenv tl)
  | GramConstrNonTerminal (typ, Some _) :: tl ->
      (* parse a binding non-terminal *)
    (match typ with
    | ETConstr _ -> (* pattern non-terminal *)
        Gram.action (fun (v:cases_pattern_expr) ->
          make (v::env, envlist, hasbinders) tl)
    | ETReference ->
        Gram.action (fun (v:reference) ->
	  make (CPatAtom (Loc.ghost,Some v) :: env, envlist, hasbinders) tl)
    | ETName ->
        Gram.action (fun (na:Loc.t * Name.t) ->
	  make (cases_pattern_expr_of_name na :: env, envlist, hasbinders) tl)
    | ETBigint ->
        Gram.action (fun (v:Bigint.bigint) ->
	  make (CPatPrim (Loc.ghost,Numeral v) :: env, envlist, hasbinders) tl)
    | ETConstrList (_,_) ->
        Gram.action  (fun (vl:cases_pattern_expr list) ->
	  make (env, vl :: envlist, hasbinders) tl)
    | ETBinder _ | ETBinderList (true,_) ->
	Gram.action (fun (v:local_binder list) ->
	  make (env, envlist, hasbinders) tl)
    | ETBinderList (false,_) ->
	Gram.action (fun (v:local_binder list list) ->
	  make (env, envlist, true) tl)
    | (ETPattern | ETOther _) ->
        anomaly (Pp.str "Unexpected entry of type cases pattern or other"))
  | GramConstrListMark (n,b) :: tl ->
      (* Rebuild expansions of ConstrList *)
      let heads,env = List.chop n env in
      if b then
        make (env,(heads@List.hd envlist)::List.tl envlist,hasbinders) tl
      else
        make (env,heads::envlist,hasbinders) tl
  in
  make ([],[],false) (List.rev pil)

let rec make_constr_prod_item assoc from forpat = function
  | GramConstrTerminal tok :: l ->
      gram_token_of_token tok :: make_constr_prod_item assoc from forpat l
  | GramConstrNonTerminal (nt, ovar) :: l ->
      symbol_of_constr_prod_entry_key assoc from forpat nt
      :: make_constr_prod_item assoc from forpat l
  | GramConstrListMark _ :: l ->
      make_constr_prod_item assoc from forpat l
  | [] ->
      []

let prepare_empty_levels forpat (pos,p4assoc,name,reinit) =
  let entry =
    if forpat then weaken_entry Constr.pattern
    else weaken_entry Constr.operconstr in
  grammar_extend entry reinit (pos,[(name, p4assoc, [])])

let pure_sublevels level symbs =
  let filter s =
    try
      let i = level_of_snterml s in
      begin match level with
      | Some j when Int.equal i j -> None
      | _ -> Some i
      end
    with Failure _ -> None
  in
  List.map_filter filter symbs

let extend_constr (entry,level) (n,assoc) mkact forpat rules =
  List.fold_left (fun nb pt ->
  let symbs = make_constr_prod_item assoc n forpat pt in
  let pure_sublevels = pure_sublevels level symbs in
  let needed_levels = register_empty_levels forpat pure_sublevels in
  let map_level (pos, ass1, name, ass2) =
    (Option.map of_coq_position pos, Option.map of_coq_assoc ass1, name, ass2) in
  let needed_levels = List.map map_level needed_levels in
  let pos,p4assoc,name,reinit = find_position forpat assoc level in
  let nb_decls = List.length needed_levels + 1 in
  List.iter (prepare_empty_levels forpat) needed_levels;
  grammar_extend entry reinit (Option.map of_coq_position pos,
    [(name, Option.map of_coq_assoc p4assoc, [symbs, mkact pt])]);
  nb_decls) 0 rules

type notation_grammar = {
  notgram_level : int;
  notgram_assoc : gram_assoc option;
  notgram_notation : notation;
  notgram_prods : grammar_constr_prod_item list list
}

let extend_constr_constr_notation ng =
  let level = ng.notgram_level in
  let mkact loc env = CNotation (loc, ng.notgram_notation, env) in
  let e = interp_constr_entry_key false (ETConstr (level, ())) in
  let ext = (ETConstr (level, ()), ng.notgram_assoc) in
  extend_constr e ext (make_constr_action mkact) false ng.notgram_prods

let extend_constr_pat_notation ng =
  let level = ng.notgram_level in
  let mkact loc env = CPatNotation (loc, ng.notgram_notation, env, []) in
  let e = interp_constr_entry_key true (ETConstr (level, ())) in
  let ext = ETConstr (level, ()), ng.notgram_assoc in
  extend_constr e ext (make_cases_pattern_action mkact) true ng.notgram_prods

let extend_constr_notation ng =
  (* Add the notation in constr *)
  let nb = extend_constr_constr_notation ng in
  (* Add the notation in cases_pattern *)
  let nb' = extend_constr_pat_notation ng in
  nb + nb'

(**********************************************************************)
(** Grammar declaration for Tactic Notation (Coq level)               *)

let get_tactic_entry n =
  if Int.equal n 0 then
    weaken_entry Tactic.simple_tactic, None
  else if Int.equal n 5 then
    weaken_entry Tactic.binder_tactic, None
  else if 1<=n && n<5 then
    weaken_entry Tactic.tactic_expr, Some (Extend.Level (string_of_int n))
  else
    error ("Invalid Tactic Notation level: "^(string_of_int n)^".")

(**********************************************************************)
(** State of the grammar extensions                                   *)

type tactic_grammar = {
  tacgram_key : string;
  tacgram_level : int;
  tacgram_prods : grammar_prod_item list;
  tacgram_tactic : DirPath.t * Tacexpr.glob_tactic_expr;
}

type all_grammar_command =
  | Notation of
	 (precedence * tolerability list) *
	  notation_var_internalization_type list *
	  notation_grammar
  | TacticGrammar of tactic_grammar

(* Declaration of the tactic grammar rule *)

let head_is_ident tg = match tg.tacgram_prods with
| GramTerminal _::_ -> true
| _ -> false

let add_tactic_entry tg =
  let entry, pos = get_tactic_entry tg.tacgram_level in
  let rules =
    if Int.equal tg.tacgram_level 0 then begin
      if not (head_is_ident tg) then
        error "Notation for simple tactic must start with an identifier.";
      let mkact loc l =
        (TacAlias (loc,tg.tacgram_key,l,tg.tacgram_tactic):raw_atomic_tactic_expr) in
      make_rule mkact tg.tacgram_prods
    end
    else
      let mkact loc l =
        (TacAtom(loc,TacAlias(loc,tg.tacgram_key,l,tg.tacgram_tactic)):raw_tactic_expr) in
      make_rule mkact tg.tacgram_prods in
  synchronize_level_positions ();
  grammar_extend entry None (Option.map of_coq_position pos,[(None, None, List.rev [rules])]);
  1

let (grammar_state : (int * all_grammar_command) list ref) = ref []

let extend_grammar gram =
  let nb = match gram with
  | Notation (_,_,a) -> extend_constr_notation a
  | TacticGrammar g -> add_tactic_entry g in
  grammar_state := (nb,gram) :: !grammar_state

let recover_notation_grammar ntn prec =
  let filter = function
  | _, Notation (prec', vars, ng) when
      Notation.level_eq prec prec' &&
      String.equal ntn ng.notgram_notation -> Some (vars, ng)
  | _ -> None
  in
  match List.map_filter filter !grammar_state with
  | [x] -> x
  | _ -> assert false

(* Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t = (int * all_grammar_command) list * Lexer.frozen_t

let freeze _ : frozen_t = (!grammar_state, Lexer.freeze ())

(* We compare the current state of the grammar and the state to unfreeze,
   by computing the longest common suffixes *)
let factorize_grams l1 l2 =
  if l1 == l2 then ([], [], l1) else List.share_tails l1 l2

let number_of_entries gcl =
  List.fold_left (fun n (p,_) -> n + p) 0 gcl

let unfreeze (grams, lex) =
  let (undo, redo, common) = factorize_grams !grammar_state grams in
  let n = number_of_entries undo in
  remove_grammars n;
  remove_levels n;
  grammar_state := common;
  Lexer.unfreeze lex;
  List.iter extend_grammar (List.rev_map snd redo)

(** No need to provide an init function : the grammar state is
    statically available, and already empty initially, while
    the lexer state should not be resetted, since it contains
    keywords declared in g_*.ml4 *)

let _ =
  Summary.declare_summary "GRAMMAR_LEXER"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

let with_grammar_rule_protection f x =
  let fs = freeze false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Errors.push reraise in
    let () = unfreeze fs in
    raise reraise
