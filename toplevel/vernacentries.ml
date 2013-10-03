(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open Errors
open Util
open Flags
open Names
open Nameops
open Term
open Pfedit
open Tacmach
open Constrintern
open Prettyp
open Printer
open Tacinterp
open Command
open Goptions
open Libnames
open Globnames
open Vernacexpr
open Decl_kinds
open Constrexpr
open Redexpr
open Lemmas
open Declaremods
open Misctypes
open Locality

(* Misc *)

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_global (Smartlocate.smart_global r)

let scope_class_of_qualid qid =
  Notation.scope_class_of_reference (Smartlocate.smart_global qid)

(*******************)
(* "Show" commands *)

let show_proof () =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  let p = Proof_global.give_me_the_proof () in
  let pprf = Proof.partial_proof p in
  msg_notice (Pp.prlist_with_sep Pp.fnl Printer.pr_constr pprf)

let show_node () =
  (* spiwack: I'm have little clue what this function used to do. I deactivated it, 
      could, possibly, be cleaned away. (Feb. 2010) *)
  ()

(* indentation code for Show Script, initially contributed
   by D. de Rauglaudre *)

let indent_script_item ((ng1,ngl1),nl,beginend,ppl) (cmd,ng) =
  (* ng1 : number of goals remaining at the current level (before cmd)
     ngl1 : stack of previous levels with their remaining goals
     ng : number of goals after the execution of cmd
     beginend : special indentation stack for { } *)
  let ngprev = List.fold_left (+) ng1 ngl1 in
  let new_ngl =
    if ng > ngprev then
      (* We've branched *)
      (ng - ngprev + 1, ng1 - 1 :: ngl1)
    else if ng < ngprev then
      (* A subgoal have been solved. Let's compute the new current level
	 by discarding all levels with 0 remaining goals. *)
      let _ = assert (Int.equal ng (ngprev - 1)) in
      let rec loop = function
	| (0, ng2::ngl2) -> loop (ng2,ngl2)
	| p -> p
      in loop (ng1-1, ngl1)
    else
      (* Standard case, same goal number as before *)
      (ng1, ngl1)
  in
  (* When a subgoal have been solved, separate this block by an empty line *)
  let new_nl = (ng < ngprev)
  in
  (* Indentation depth *)
  let ind = List.length ngl1
  in
  (* Some special handling of bullets and { }, to get a nicer display *)
  let pred n = max 0 (n-1) in
  let ind, nl, new_beginend = match cmd with
    | VernacSubproof _ -> pred ind, nl, (pred ind)::beginend
    | VernacEndSubproof -> List.hd beginend, false, List.tl beginend
    | VernacBullet _ -> pred ind, nl, beginend
    | _ -> ind, nl, beginend
  in
  let pp =
    (if nl then fnl () else mt ()) ++
    (hov (ind+1) (str (String.make ind ' ') ++ Ppvernac.pr_vernac cmd))
  in
  (new_ngl, new_nl, new_beginend, pp :: ppl)

let show_script () =
  let prf = Pfedit.get_current_proof_name () in
  let cmds = Backtrack.get_script prf in
  let _,_,_,indented_cmds =
    List.fold_left indent_script_item ((1,[]),false,[],[]) cmds
  in
  let indented_cmds = List.rev (indented_cmds) in
  msg_notice (v 0 (Pp.prlist_with_sep Pp.fnl (fun x -> x) indented_cmds))

let show_thesis () =
     msg_error (anomaly (Pp.str "TODO") )

let show_top_evars () =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let pfts = get_pftreestate () in
  let gls = Proof.V82.subgoals pfts in
  let sigma = gls.Evd.sigma in
  msg_notice (pr_evars_int 1 (Evarutil.non_instantiated sigma))

let show_prooftree () =
  (* Spiwack: proof tree is currently not working *)
  ()

let enable_goal_printing = ref true

let print_subgoals () =
  if !enable_goal_printing && is_verbose ()
  then msg_notice (pr_open_subgoals ())

let try_print_subgoals () =
  Pp.flush_all();
  try print_subgoals () with Proof_global.NoCurrentProof | UserError _ -> ()


  (* Simulate the Intro(s) tactic *)

let show_intro all =
  let pf = get_pftreestate() in
  let {Evd.it=gls ; sigma=sigma} = Proof.V82.subgoals pf in
  let gl = {Evd.it=List.hd gls ; sigma = sigma} in
  let l,_= decompose_prod_assum (strip_outer_cast (pf_concl gl)) in
  if all
  then
    let lid = Tactics.find_intro_names l gl in
    msg_notice (hov 0 (prlist_with_sep  spc pr_id lid))
  else
    try
      let n = List.last l in
      msg_notice (pr_id (List.hd (Tactics.find_intro_names [n] gl)))
    with Failure "List.last" -> ()

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

let make_cases s =
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  match glob_ref with
    | Globnames.IndRef i ->
	let {Declarations.mind_nparams = np}
	    , {Declarations.mind_consnames = carr ; Declarations.mind_nf_lc = tarr }
	      = Global.lookup_inductive i in
	Util.Array.fold_right2
	  (fun consname typ l ->
	     let al = List.rev (fst (decompose_prod typ)) in
	     let al = Util.List.skipn np al in
	     let rec rename avoid = function
	       | [] -> []
	       | (n,_)::l ->
		   let n' = Namegen.next_name_away_in_cases_pattern n avoid in
		   Id.to_string n' :: rename (n'::avoid) l in
	     let al' = rename [] al in
	     (Id.to_string consname :: al') :: l)
	  carr tarr []
    | _ -> raise Not_found

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try make_cases (Id.to_string (snd id))
    with Not_found -> error "Unknown inductive type."
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  msg_notice (v 1 (str "match # with" ++ fnl () ++
	    prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ()))

(* "Print" commands *)

let print_path_entry p =
  let dir = str (DirPath.to_string (Loadpath.logical p)) in
  let path = str (Loadpath.physical p) in
  (dir ++ str " " ++ tbrk (0, 0) ++ path)

let print_loadpath dir =
  let l = Loadpath.get_load_paths () in
  let l = match dir with
  | None -> l
  | Some dir ->
    let filter p = is_dirpath_prefix_of dir (Loadpath.logical p) in
    List.filter filter l
  in
  Pp.t (str "Logical Path:                 " ++
                tab () ++ str "Physical path:" ++ fnl () ++
                prlist_with_sep fnl print_path_entry l)

let print_modules () =
  let opened = Library.opened_libraries ()
  and loaded = Library.loaded_libraries () in
  (* we intersect over opened to preserve the order of opened since *)
  (* non-commutative operations (e.g. visibility) are done at import time *)
  let loaded_opened = List.intersect opened loaded
  and only_loaded = List.subtract loaded opened in
  str"Loaded and imported library files: " ++
  pr_vertical_list pr_dirpath loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list pr_dirpath only_loaded


let print_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let globdir = Nametab.locate_dir qid in
      match globdir with
	  DirModule (dirpath,(mp,_)) ->
	    msg_notice (Printmod.print_module (Printmod.printable_body dirpath) mp)
	| _ -> raise Not_found
  with
      Not_found -> msg_error (str"Unknown Module " ++ pr_qualid qid)

let print_modtype r =
  let (loc,qid) = qualid_of_reference r in
  try
    let kn = Nametab.locate_modtype qid in
    msg_notice (Printmod.print_modtype kn)
  with Not_found ->
    (* Is there a module of this name ? If yes we display its type *)
    try
      let mp = Nametab.locate_module qid in
      msg_notice (Printmod.print_module false mp)
    with Not_found ->
      msg_error (str"Unknown Module Type or Module " ++ pr_qualid qid)

let print_namespace ns =
  let ns = List.rev (Names.DirPath.repr ns) in
  (* [match_dirpath], [match_modulpath] are helpers for [matches]
     which checks whether a constant is in the namespace [ns]. *)
  let rec match_dirpath ns = function
    | [] -> Some ns
    | id::dir ->
        begin match match_dirpath ns dir with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  let rec match_modulepath ns = function
    | MPbound _ -> None (* Not a proper namespace. *)
    | MPfile dir -> match_dirpath ns (Names.DirPath.repr dir)
    | MPdot (mp,lbl) ->
        let id = Names.Label.to_id lbl in
        begin match match_modulepath ns mp with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  (* [qualified_minus n mp] returns a list of qualifiers representing
     [mp] except the [n] first (in the concrete syntax order).  The
     idea is that if [mp] matches [ns], then [qualified_minus mp
     (length ns)] will be the correct representation of [mp] assuming
     [ns] is imported. *)
  (* precondition: [mp] matches some namespace of length [n] *)
  let qualified_minus n mp =
    let rec list_of_modulepath = function
      | MPbound _ -> assert false (* MPbound never matches *)
      | MPfile dir -> Names.DirPath.repr dir
      | MPdot (mp,lbl) -> (Names.Label.to_id lbl)::(list_of_modulepath mp)
    in
    snd (Util.List.chop n (List.rev (list_of_modulepath mp)))
  in
  let print_list pr l = prlist_with_sep (fun () -> str".") pr l in
  let print_kn kn =
    (* spiwack: I'm ignoring the dirpath, is that bad? *)
    let (mp,_,lbl) = Names.repr_kn kn in
    let qn = (qualified_minus (List.length ns) mp)@[Names.Label.to_id lbl] in
    print_list pr_id qn
  in
  let print_constant k body =
    let t = body.Declarations.const_type in
    print_kn k ++ str":" ++ spc() ++ Printer.pr_type t
  in
  let matches mp = match match_modulepath ns mp with
  | Some [] -> true
  | _ -> false in
  let constants = (Environ.pre_env (Global.env ())).Pre_env.env_globals.Pre_env.env_constants in
  let constants_in_namespace =
    Cmap_env.fold (fun c (body,_) acc ->
      let kn = user_con c in
      if matches (modpath kn) then
        acc++fnl()++hov 2 (print_constant kn body)
      else
        acc
    ) constants (str"")
  in
  msg_notice ((print_list pr_id ns)++str":"++fnl()++constants_in_namespace)

let dump_universes_gen g s =
  let output = open_out s in
  let output_constraint, close =
    if Filename.check_suffix s ".dot" || Filename.check_suffix s ".gv" then begin
      (* the lazy unit is to handle errors while printing the first line *)
      let init = lazy (Printf.fprintf output "digraph universes {\n") in
      begin fun kind left right ->
        let () = Lazy.force init in
        match kind with
          | Univ.Lt ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=bold];\n" right left
          | Univ.Le ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=solid];\n" right left
          | Univ.Eq ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=dashed];\n" left right
      end, begin fun () ->
        if Lazy.lazy_is_val init then Printf.fprintf output "}\n";
        close_out output
      end
    end else begin
      begin fun kind left right ->
        let kind = match kind with
          | Univ.Lt -> "<"
          | Univ.Le -> "<="
          | Univ.Eq -> "="
        in Printf.fprintf output "%s %s %s ;\n" left kind right
      end, (fun () -> close_out output)
    end
  in
  try
    Univ.dump_universes output_constraint g;
    close ();
    msg_info (str ("Universes written to file \""^s^"\"."))
  with reraise -> close (); raise reraise

let dump_universes sorted s =
  let g = Global.universes () in
  let g = if sorted then Univ.sort_universes g else g in
  dump_universes_gen g s

(*********************)
(* "Locate" commands *)

let locate_file f =
  let paths = Loadpath.get_paths () in
  let _, file = System.find_file_in_path ~warn:false paths f in
  str file

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      msg_info (hov 0
	(pr_dirpath fulldir ++ strbrk " has been loaded from file " ++
	 str file))
  | Library.LibInPath, fulldir, file ->
      msg_info (hov 0
	(pr_dirpath fulldir ++ strbrk " is bound to file " ++ str file))

let err_unmapped_library loc qid =
  let dir = fst (repr_qualid qid) in
  user_err_loc
    (loc,"locate_library",
     strbrk "Cannot find a physical path bound to logical path " ++
       pr_dirpath dir ++ str".")

let err_notfound_library loc qid =
  msg_error
    (hov 0 (strbrk "Unable to locate library " ++ pr_qualid qid ++ str"."))

let print_located_library r =
  let (loc,qid) = qualid_of_reference r in
  try msg_found_library (Library.locate_qualified_library false qid)
  with
    | Library.LibUnmappedDir -> err_unmapped_library loc qid
    | Library.LibNotFound -> err_notfound_library loc qid

let print_located_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let dir = Nametab.full_name_module qid in
    msg_notice (str "Module " ++ pr_dirpath dir)
  with Not_found ->
    if DirPath.is_empty (fst (repr_qualid qid)) then
      msg_error (str "No module is referred to by basename" ++ spc () ++ pr_qualid qid)
    else
      msg_error (str "No module is referred to by name" ++ spc () ++ pr_qualid qid)

let print_located_tactic r =
  let (loc,qid) = qualid_of_reference r in
  try
    let path = Nametab.path_of_tactic (Nametab.locate_tactic qid) in
    msg_notice (str "Ltac " ++ pr_path path)
  with Not_found ->
    msg_error (str "No Ltac definition is referred to by " ++ pr_qualid qid)

let smart_global r =
  let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob (Genarg.loc_of_or_by_notation loc_of_reference r) gr;
    gr

let dump_global r =
  try
    let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob (Genarg.loc_of_or_by_notation loc_of_reference r) gr
  with e when Errors.noncritical e -> ()
(**********)
(* Syntax *)

let vernac_syntax_extension locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_syntax_extension local

let vernac_delimiters = Metasyntax.add_delimiters

let vernac_bind_scope sc cll =
  Metasyntax.add_class_scope sc (List.map scope_class_of_qualid cll)

let vernac_open_close_scope locality local (b,s) =
  let local = enforce_section_locality locality local in
  Notation.open_close_scope (local,b,s)

let vernac_arguments_scope locality r scl =
  let local = make_section_locality locality in
  Notation.declare_arguments_scope local (smart_global r) scl

let vernac_infix locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_infix local

let vernac_notation locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_notation local

(***********)
(* Gallina *)

let start_proof_and_print k l hook =
  start_proof_com k l hook;
  print_subgoals ()

let no_hook _ _ = ()

let vernac_definition_hook p = function
| Coercion -> Class.add_coercion_hook p
| CanonicalStructure -> fun _ -> Recordops.declare_canonical_structure
| SubClass -> Class.add_subclass_hook p
| _ -> no_hook

let vernac_definition locality p (local,k) (loc,id as lid) def =
  let local = enforce_locality_exp locality local in
  let hook = vernac_definition_hook p k in
  let () = match local with
  | Discharge -> Dumpglob.dump_definition lid true "var"
  | Local | Global -> Dumpglob.dump_definition lid false "def"
  in
  (match def with
    | ProveBody (bl,t) ->   (* local binders, typ *)
 	  start_proof_and_print (local,p,DefinitionBody Definition)
	    [Some lid, (bl,t,None)] no_hook
    | DefineBody (bl,red_option,c,typ_opt) ->
 	let red_option = match red_option with
          | None -> None
          | Some r ->
	      let (evc,env)= get_current_context () in
 		Some (snd (interp_redexp env evc r)) in
	do_definition id (local,p,k) bl red_option c typ_opt hook)

let vernac_start_proof p kind l lettop =
  if Dumpglob.dump () then
    List.iter (fun (id, _) ->
      match id with
	| Some lid -> Dumpglob.dump_definition lid false "prf"
	| None -> ()) l;
  if not(refining ()) then
    if lettop then
      errorlabstrm "Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode.");
  start_proof_and_print (Global, p, Proof kind) l no_hook

let qed_display_script = ref true

let vernac_end_proof = function
  | Admitted ->
    Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
    admit ();
    Pp.feedback Interface.AddedAxiom
  | Proved (is_opaque,idopt) ->
    let prf = Pfedit.get_current_proof_name () in
    if is_verbose () && !qed_display_script then show_script ();
    begin match idopt with
    | None -> save_named is_opaque
    | Some ((_,id),None) -> save_anonymous is_opaque id
    | Some ((_,id),Some kind) -> save_anonymous_with_strength kind is_opaque id
    end;
    Backtrack.mark_unreachable [prf]

  (* A stupid macro that should be replaced by ``Exact c. Save.'' all along
     the theories [??] *)

let vernac_exact_proof c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the begining of a proof. *)
  let prf = Pfedit.get_current_proof_name () in
  by (Tactics.exact_proof c);
  save_named true;
  Backtrack.mark_unreachable [prf]

let vernac_assumption locality poly (local, kind) l nl =
  let local = enforce_locality_exp locality local in
  let global = local == Global in
  let kind = local, poly, kind in
  List.iter (fun (is_coe,(idl,c)) ->
    if Dumpglob.dump () then
      List.iter (fun lid ->
	if global then Dumpglob.dump_definition lid false "ax"
	else Dumpglob.dump_definition lid true "var") idl) l;
  let status = do_assumptions kind nl l in
  if not status then Pp.feedback Interface.AddedAxiom

let vernac_record k poly finite infer struc binders sort nameopt cfs =
  let const = match nameopt with
    | None -> add_prefix "Build_" (snd (snd struc))
    | Some (_,id as lid) ->
	Dumpglob.dump_definition lid false "constr"; id in
    if Dumpglob.dump () then (
      Dumpglob.dump_definition (snd struc) false "rec";
      List.iter (fun (((_, x), _), _) ->
	match x with
	| Vernacexpr.AssumExpr ((loc, Name id), _) -> Dumpglob.dump_definition (loc,id) false "proj"
	| _ -> ()) cfs);
    ignore(Record.definition_structure (k,poly,finite,infer,struc,binders,cfs,const,sort))

let vernac_inductive poly finite infer indl =
  if Dumpglob.dump () then
    List.iter (fun (((coe,lid), _, _, _, cstrs), _) ->
      match cstrs with
	| Constructors cstrs ->
	    Dumpglob.dump_definition lid false "ind";
	    List.iter (fun (_, (lid, _)) ->
			 Dumpglob.dump_definition lid false "constr") cstrs
	| _ -> () (* dumping is done by vernac_record (called below) *) )
      indl;
  match indl with
  | [ ( id , bl , c , b, RecordDecl (oc,fs) ), [] ] ->
      vernac_record (match b with Class true -> Class false | _ -> b)
	poly finite infer id bl c oc fs
  | [ ( id , bl , c , Class true, Constructors [l]), _ ] ->
      let f =
	let (coe, ((loc, id), ce)) = l in
	let coe' = if coe then Some true else None in
	  (((coe', AssumExpr ((loc, Name id), ce)), None), [])
      in vernac_record (Class true) poly finite infer id bl c None [f]
  | [ ( id , bl , c , Class true, _), _ ] ->
      Errors.error "Definitional classes must have a single method"
  | [ ( id , bl , c , Class false, Constructors _), _ ] ->
      Errors.error "Inductive classes not supported"
  | [ ( _ , _ , _ , _, RecordDecl _ ) , _ ] ->
      Errors.error "where clause not supported for (co)inductive records"
  | _ -> let unpack = function
      | ( (_, id) , bl , c , _ , Constructors l ) , ntn  -> ( id , bl , c , l ) , ntn
      | _ -> Errors.error "Cannot handle mutually (co)inductive records."
    in
    let indl = List.map unpack indl in
    do_mutual_inductive indl poly (finite != CoFinite)

let vernac_fixpoint locality poly local l =
  let local = enforce_locality_exp locality local in
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_fixpoint local poly l

let vernac_cofixpoint locality poly local l =
  let local = enforce_locality_exp locality local in
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_cofixpoint local poly l

let vernac_scheme l =
  if Dumpglob.dump () then
    List.iter (fun (lid, s) ->
	       Option.iter (fun lid -> Dumpglob.dump_definition lid false "def") lid;
	       match s with
	       | InductionScheme (_, r, _)
	       | CaseScheme (_, r, _) 
	       | EqualityScheme r -> dump_global r) l;
  Indschemes.do_scheme l

let vernac_combined_scheme lid l =
  if Dumpglob.dump () then
    (Dumpglob.dump_definition lid false "def";
     List.iter (fun lid -> dump_global (Misctypes.AN (Ident lid))) l);
 Indschemes.do_combined_scheme lid l

(**********************)
(* Modules            *)

let vernac_import export refl =
  let import ref =
    Library.import_module export (qualid_of_reference ref)
  in
    List.iter import refl;
    Lib.add_frozen_state ()

let vernac_declare_module export (loc, id) binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      error ("Arguments of a functor declaration cannot be exported. " ^
       "Remove the \"Export\" and \"Import\" keywords from every functor " ^
       "argument.")
     else (idl,ty)) binders_ast in
  let mp = Declaremods.declare_module
    Modintern.interp_modtype Modintern.interp_modexpr
    Modintern.interp_modexpr_or_modtype
    id binders_ast (Enforce mty_ast) []
  in
    Dumpglob.dump_moddef loc mp "mod";
    if_verbose msg_info (str ("Module "^ Id.to_string id ^" is declared"));
    Option.iter (fun export -> vernac_import export [Ident (Loc.ghost,id)]) export

let vernac_define_module export (loc, id) binders_ast mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  match mexpr_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp = Declaremods.start_module Modintern.interp_modtype export
	 id binders_ast mty_ast_o
       in
	 Dumpglob.dump_moddef loc mp "mod";
	 if_verbose msg_info
	   (str ("Interactive Module "^ Id.to_string id ^" started"));
         List.iter
           (fun (export,id) ->
             Option.iter
               (fun export -> vernac_import export [Ident (Loc.ghost,id)]) export
           ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           error ("Arguments of a functor definition can be imported only if" ^
                  " the definition is interactive. Remove the \"Export\" and " ^
                  "\"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp =	Declaremods.declare_module
	  Modintern.interp_modtype Modintern.interp_modexpr
          Modintern.interp_modexpr_or_modtype
	  id binders_ast mty_ast_o mexpr_ast_l
       in
	 Dumpglob.dump_moddef loc mp "mod";
	 if_verbose msg_info
	   (str ("Module "^ Id.to_string id ^" is defined"));
         Option.iter (fun export -> vernac_import export [Ident (Loc.ghost,id)])
           export

let vernac_end_module export (loc,id as lid) =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref loc mp "mod";
  if_verbose msg_info (str ("Module "^ Id.to_string id ^" is defined"));
  Option.iter (fun export -> vernac_import export [Ident lid]) export

let vernac_declare_module_type (loc,id) binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";

  match mty_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =       
	 List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       
       let mp = Declaremods.start_modtype
	 Modintern.interp_modtype id binders_ast mty_sign in
        Dumpglob.dump_moddef loc mp "modtype";
	if_verbose msg_info
	  (str ("Interactive Module Type "^ Id.to_string id ^" started"));
        List.iter
         (fun (export,id) ->
           Option.iter
            (fun export -> vernac_import export [Ident (Loc.ghost,id)]) export
         ) argsexport

    | _ :: _ ->
	let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              error ("Arguments of a functor definition can be imported only if" ^
			" the definition is interactive. Remove the \"Export\" " ^
			"and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
	let mp = Declaremods.declare_modtype Modintern.interp_modtype
          Modintern.interp_modexpr_or_modtype
	  id binders_ast mty_sign mty_ast_l in
          Dumpglob.dump_moddef loc mp "modtype";
	  if_verbose msg_info
	    (str ("Module Type "^ Id.to_string id ^" is defined"))

let vernac_end_modtype (loc,id) =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref loc mp "modtype";
  if_verbose msg_info (str ("Module Type "^ Id.to_string id ^" is defined"))

let vernac_include l =
  Declaremods.declare_include Modintern.interp_modexpr_or_modtype l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section (_, id as lid) =
  check_no_pending_proofs ();
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section (loc,_) =
  Dumpglob.dump_reference loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

(* Dispatcher of the "End" command *)

let vernac_end_segment (_,id as lid) =
  check_no_pending_proofs ();
  match Lib.find_opening_node id with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

(* Libraries *)

let vernac_require import qidl =
  let qidl = List.map qualid_of_reference qidl in
  let modrefl = Flags.silently (List.map Library.try_locate_qualified_library) qidl in
  if Dumpglob.dump () then
    List.iter2 (fun (loc, _) dp -> Dumpglob.dump_libref loc dp "lib") qidl (List.map fst modrefl);
  Library.require_library_from_dirpath modrefl import

(* Coercions and canonical structures *)

let vernac_canonical r =
  Recordops.declare_canonical_structure (smart_global r)

let vernac_coercion locality poly local ref qids qidt =
  let local = enforce_locality locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  Class.try_add_new_coercion_with_target ref' ~local poly ~source ~target;
  if_verbose msg_info (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion locality poly local id qids qidt =
  let local = enforce_locality locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id ~local poly ~source ~target

(* Type classes *)

let vernac_instance abst locality poly sup inst props pri =
  let glob = not (make_section_locality locality) in
  Dumpglob.dump_constraint inst false "inst";
  ignore(Classes.new_instance ~abstract:abst ~global:glob poly sup inst props pri)

let vernac_context l =
  if not (Classes.context l) then Pp.feedback Interface.AddedAxiom

let vernac_declare_instances locality ids =
  let glob = not (make_section_locality locality) in
  List.iter (fun (id) -> Classes.existing_instance glob id) ids

let vernac_declare_class id =
  Classes.declare_class id

(***********)
(* Solving *)

let command_focus = Proof.new_focus_kind ()
let focus_command_cond = Proof.no_cond command_focus


let vernac_solve n tcom b =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
  let p = Proof_global.give_me_the_proof () in
  Proof.transaction p begin fun () ->
    solve_nth n (Tacinterp.hide_interp tcom None) ~with_end_tac:b;
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    Proof_global.maximal_unfocus command_focus p;
    print_subgoals()
  end
 

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since
     all tactics fail if there are no further goals to prove. *)

let vernac_solve_existential = instantiate_nth_evar_com

let vernac_set_end_tac tac =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
  match tac with
  | Tacexpr.TacId [] -> ()
  | _ -> set_end_tac (Tacinterp.interp tac)
    (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)

let vernac_set_used_variables l =
  let l = List.map snd l in
  if not (List.distinct l) then error "Used variables list contains duplicates";
  let vars = Environ.named_context (Global.env ()) in
  List.iter (fun id -> 
    if not (List.exists (fun (id',_,_) -> Id.equal id id') vars) then
      error ("Unknown variable: " ^ Id.to_string id))
    l;
  set_used_variables l

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> msg_warning (str x)) filename

let vernac_require_from export filename =
  Library.require_library_from_file None (expand filename) export

let vernac_add_loadpath isrec pdir ldiropt =
  let pdir = expand pdir in
  let alias = Option.default Nameops.default_root_prefix ldiropt in
  (if isrec then Mltop.add_rec_path else Mltop.add_path)
    ~unix_path:pdir ~coq_root:alias

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir) (expand path)

let vernac_declare_ml_module locality l =
  let local = make_locality locality in
  Mltop.declare_ml_modules local (List.map expand l)

let vernac_chdir = function
  | None -> msg_notice (str (Sys.getcwd()))
  | Some path ->
      begin
	try Sys.chdir (expand path)
	with Sys_error err -> msg_warning (str ("Cd failed: " ^ err))
      end;
      if_verbose msg_info (str (Sys.getcwd()))


(********************)
(* State management *)

let vernac_write_state file =
  Pfedit.delete_all_proofs ();
  States.extern_state file

let vernac_restore_state file =
  Pfedit.delete_all_proofs ();
  States.intern_state file

(************)
(* Commands *)

let vernac_declare_tactic_definition locality (x,def) =
  let local = make_module_locality locality in
  Tacintern.add_tacdef local x def

let vernac_create_hintdb locality id b =
  let local = make_module_locality locality in
  Auto.create_hint_db local id full_transparent_state b

let vernac_remove_hints locality dbs ids =
  let local = make_module_locality locality in
  Auto.remove_hints local dbs (List.map Smartlocate.global_with_alias ids)

let vernac_hints locality poly local lb h =
  let local = enforce_module_locality locality local in
  Auto.add_hints local lb (Auto.interp_hints poly h)

let vernac_syntactic_definition locality lid x local y =
  Dumpglob.dump_definition lid false "syndef";
  let local = enforce_module_locality locality local in
  Metasyntax.add_syntactic_definition (snd lid) x local y

let vernac_declare_implicits locality r l =
  let local = make_section_locality locality in
  match l with
  | [] ->
      Impargs.declare_implicits local (smart_global r)
  | _::_ as imps ->
      Impargs.declare_manual_implicits local (smart_global r) ~enriching:false
	(List.map (List.map (fun (ex,b,f) -> ex, (b,true,f))) imps)

let vernac_declare_arguments locality r l nargs flags =
  let extra_scope_flag = List.mem `ExtraScopes flags in
  let names = List.map (List.map (fun (id, _,_,_,_) -> id)) l in
  let names, rest = List.hd names, List.tl names in
  let scopes = List.map (List.map (fun (_,_, s, _,_) -> s)) l in
  if List.exists (fun na -> not (List.equal Name.equal na names)) rest then
    error "All arguments lists must declare the same names.";
  if not (List.distinct (List.filter ((!=) Anonymous) names)) then
    error "Arguments names must be distinct.";
  let sr = smart_global r in
  let inf_names =
    let ty = Global.type_of_global_unsafe sr in
      Impargs.compute_implicits_names (Global.env ()) ty in
  let string_of_name = function Anonymous -> "_" | Name id -> Id.to_string id in
  let rec check li ld ls = match li, ld, ls with
    | [], [], [] -> ()
    | [], Anonymous::ld, (Some _)::ls when extra_scope_flag -> check li ld ls
    | [], _::_, (Some _)::ls when extra_scope_flag ->
       error "Extra notation scopes can be set on anonymous arguments only"
    | [], x::_, _ -> error ("Extra argument " ^ string_of_name x ^ ".")
    | l, [], _ -> error ("The following arguments are not declared: " ^
       (String.concat ", " (List.map string_of_name l)) ^ ".")
    | _::li, _::ld, _::ls -> check li ld ls 
    | _ -> assert false in
  let () = match l with
  | [[]] -> ()
  | _ ->
    List.iter2 (fun l -> check inf_names l) (names :: rest) scopes
  in
  (* we take extra scopes apart, and we check they are consistent *)
  let l, scopes = 
    let scopes, rest = List.hd scopes, List.tl scopes in
    if List.exists (List.exists ((!=) None)) rest then
      error "Notation scopes can be given only once";
    if not extra_scope_flag then l, scopes else
    let l, _ = List.split (List.map (List.chop (List.length inf_names)) l) in
    l, scopes in
  (* we interpret _ as the inferred names *)
  let l = match l with
  | [[]] -> l
  | _ ->
    let name_anons = function
      | (Anonymous, a,b,c,d), Name id -> Name id, a,b,c,d
      | x, _ -> x in
    List.map (fun ns -> List.map name_anons (List.combine ns inf_names)) l in
  let names_decl = List.map (List.map (fun (id, _,_,_,_) -> id)) l in
  let some_renaming_specified =
    try
      let names = Arguments_renaming.arguments_names sr in
      not (List.equal (List.equal Name.equal) names names_decl)
    with Not_found -> false in
  let some_renaming_specified, implicits =
    match l with
    | [[]] -> false, [[]]
    | _ ->
    List.fold_map (fun sr il ->
      let sr', impl = List.fold_map (fun b -> function
        | (Anonymous, _,_, true, max), Name id -> assert false
        | (Name x, _,_, true, _), Anonymous ->
            error ("Argument "^Id.to_string x^" cannot be declared implicit.")
        | (Name iid, _,_, true, max), Name id ->
           b || not (Id.equal iid id), Some (ExplByName id, max, false)
        | (Name iid, _,_, false, _), Name id ->
           if not (Id.equal iid id) then
             error("Argument "^Id.to_string id^" cannot be renamed to "^
               Id.to_string iid^" because it is not declared as implicit");
           b, None
        | _ -> b, None)
        sr (List.combine il inf_names) in
      sr || sr', List.map_filter (fun x -> x) impl)
      some_renaming_specified l in
  if some_renaming_specified then
    if not (List.mem `Rename flags) then
      error "To rename arguments the \"rename\" flag must be specified."
    else
      Arguments_renaming.rename_arguments
        (make_section_locality locality) sr names_decl;
  (* All other infos are in the first item of l *)
  let l = List.hd l in
  let some_implicits_specified = match implicits with
  | [[]] -> false | _ -> true in
  let scopes = List.map (function
    | None -> None
    | Some (o, k) ->
        try ignore (Notation.find_scope k); Some k
        with UserError _ ->
          Some (Notation.find_delimiters_scope o k)) scopes
  in
  let some_scopes_specified = List.exists ((!=) None) scopes in
  let rargs =
    Util.List.map_filter (function (n, true) -> Some n | _ -> None)
      (Util.List.map_i (fun i (_, b, _,_,_) -> i, b) 0 l) in
  if some_scopes_specified || List.mem `ClearScopes flags then
    vernac_arguments_scope locality r scopes;
  if not some_implicits_specified && List.mem `DefaultImplicits flags then
    vernac_declare_implicits locality r []
  else if some_implicits_specified || List.mem `ClearImplicits flags then
    vernac_declare_implicits locality r implicits;
  if nargs >= 0 && nargs < List.fold_left max 0 rargs then
    error "The \"/\" option must be placed after the last \"!\".";
  let rec narrow = function
    | #Tacred.simpl_flag as x :: tl -> x :: narrow tl
    | [] -> [] | _ :: tl -> narrow tl in
  let flags = narrow flags in
  if not (List.is_empty rargs) || nargs >= 0 || not (List.is_empty flags) then
    match sr with
    | ConstRef _ as c ->
       Tacred.set_simpl_behaviour
         (make_section_locality locality) c (rargs, nargs, flags)
    | _ -> errorlabstrm "" (strbrk "Modifiers of the behavior of the simpl tactic are relevant for constants only.")

let vernac_reserve bl =
  let sb_decl = (fun (idl,c) ->
    let t,ctx = Constrintern.interp_type Evd.empty (Global.env()) c in
    let t = Detyping.detype false [] [] t in
    let t = Notation_ops.notation_constr_of_glob_constr [] [] t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable locality =
  let local = make_non_locality locality in
  Implicit_quantifiers.declare_generalizable local

let _ =
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "silent";
      optkey   = ["Silent"];
      optread  = is_silent;
      optwrite = make_silent }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strict implicit arguments";
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strong strict implicit arguments";
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "contextual implicit arguments";
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit status of reversible patterns";
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "maximal insertion of implicit";
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "automatic introduction of variables";
      optkey   = ["Automatic";"Introduction"];
      optread  = Flags.is_auto_intros;
      optwrite = make_auto_intros }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "coercion printing";
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of existential variable instances";
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Constrextern.print_evar_arguments);
      optwrite = (:=) Constrextern.print_evar_arguments }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments printing";
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments defensive printing";
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "projection printing using dot notation";
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "notations printing";
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "raw printing";
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "record printing";
      optkey   = ["Printing";"Records"];
      optread  = (fun () -> !Flags.record_print);
      optwrite = (fun b -> Flags.record_print := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of the program extension";
      optkey   = ["Program";"Mode"];
      optread  = (fun () -> !Flags.program_mode);
      optwrite = (fun b -> Flags.program_mode:=b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "universe polymorphism";
      optkey   = ["Universe"; "Polymorphism"];
      optread  = Flags.is_universe_polymorphism;
      optwrite = Flags.make_universe_polymorphism }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of virtual machine inside the kernel";
      optkey   = ["Virtual";"Machine"];
      optread  = (fun () -> Vconv.use_vm ());
      optwrite = (fun b -> Vconv.set_use_vm b) }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the level of inling duging functor application";
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
	           let lev = Option.default Flags.default_inline_level o in
	           Flags.set_inline_level lev) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of boxed values";
      optkey   = ["Boxed";"Values"];
      optread  = (fun _ -> not (Vm.transp_values ()));
      optwrite = (fun b -> Vm.set_transp_values (not b)) }

(* No more undo limit in the new proof engine.
   The command still exists for compatibility (e.g. with ProofGeneral) *)

let _ =
  declare_int_option
    { optsync  = false;
      optdepr  = true;
      optname  = "the undo limit (OBSOLETE)";
      optkey   = ["Undo"];
      optread  = (fun _ -> None);
      optwrite = (fun _ -> ()) }

let _ =
  declare_int_option
    { optsync  = false;
      optdepr  = false;
      optname  = "the hypotheses limit";
      optkey   = ["Hyps";"Limit"];
      optread  = Flags.print_hyps_limit;
      optwrite = Flags.set_print_hyps_limit }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing depth";
      optkey   = ["Printing";"Depth"];
      optread  = Pp_control.get_depth_boxes;
      optwrite = Pp_control.set_depth_boxes }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing width";
      optkey   = ["Printing";"Width"];
      optread  = Pp_control.get_margin;
      optwrite = Pp_control.set_margin }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of universes";
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let vernac_debug b =
  set_debug (if b then Tactic_debug.DebugOn 0 else Tactic_debug.DebugOff)

let _ =
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Ltac debug";
      optkey   = ["Ltac";"Debug"];
      optread  = (fun () -> get_debug () != Tactic_debug.DebugOff);
      optwrite = vernac_debug }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "explicitly parsing implicit arguments";
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let vernac_set_strategy locality l =
  let local = make_locality locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity locality (v,l) =
  let local = make_non_locality locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let vernac_set_option locality key = function
  | StringValue s -> set_string_option_value_gen locality key s
  | IntValue n -> set_int_option_value_gen locality key n
  | BoolValue b -> set_bool_option_value_gen locality key b

let vernac_unset_option locality key =
  unset_option_value_gen locality key

let vernac_add_option key lv =
  let f = function
    | StringRefValue s -> (get_string_table key)#add s
    | QualidRefValue locqid -> (get_ref_table key)#add locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_remove_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#remove s
  | QualidRefValue locqid -> (get_ref_table key)#remove locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_mem_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#mem s
  | QualidRefValue locqid -> (get_ref_table key)#mem locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_print_option key =
  try (get_ref_table key)#print
  with Not_found ->
  try (get_string_table key)#print
  with Not_found ->
  try print_option_value key
  with Not_found -> error_undeclared_key key

let get_current_context_of_args = function
  | Some n -> get_goal_context n
  | None -> get_current_context ()

let vernac_check_may_eval redexp glopt rc =
  let module P = Pretype_errors in
  let (sigma, env) = get_current_context_of_args glopt in
  let sigma', c = interp_open_constr sigma env rc in
  let sigma' = Evarconv.consider_remaining_unif_problems env sigma' in
  Evarconv.check_problems_are_solved env sigma';
  let sigma',nf = Evarutil.nf_evars_and_universes sigma' in
  let c = nf c in
  let j =
    try
      Evarutil.check_evars env sigma sigma' c;
      (Arguments_renaming.rename_typing env c)
    with P.PretypeError (_,_,P.UnsolvableImplicit _) ->
      Evarutil.j_nf_evar sigma' (Retyping.get_judgment_of env sigma' c) in
  match redexp with
    | None ->
	msg_notice (print_judgment env j)
    | Some r ->
        Tacintern.dump_glob_red_expr r;
        let (sigma',r_interp) = interp_redexp env sigma' r in
	let redfun = fst (reduction_of_red_expr r_interp) in
	msg_notice (print_eval redfun env sigma' rc j)

let vernac_declare_reduction locality s r =
  let local = make_locality locality in
  declare_red_expr local s (snd (interp_redexp (Global.env()) Evd.empty r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let evmap = Evd.empty in
  let env = Global.env() in
  let c,ctx = interp_constr evmap env c in
  let senv = Global.safe_env() in
  let senv = Safe_typing.add_constraints (snd ctx) senv in
  let j = Safe_typing.typing senv c in
  msg_notice (print_safe_judgment env j)

let vernac_print = function
  | PrintTables -> msg_notice (print_tables ())
  | PrintFullContext-> msg_notice (print_full_context_typ ())
  | PrintSectionContext qid -> msg_notice (print_sec_context_typ qid)
  | PrintInspect n -> msg_notice (inspect n)
  | PrintGrammar ent -> msg_notice (Metasyntax.pr_grammar ent)
  | PrintLoadPath dir -> (* For compatibility ? *) msg_notice (print_loadpath dir)
  | PrintModules -> msg_notice (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintNamespace ns -> print_namespace ns
  | PrintMLLoadPath -> msg_notice (Mltop.print_ml_path ())
  | PrintMLModules -> msg_notice (Mltop.print_ml_modules ())
  | PrintName qid -> dump_global qid; msg_notice (print_name qid)
  | PrintGraph -> msg_notice (Prettyp.print_graph())
  | PrintClasses -> msg_notice (Prettyp.print_classes())
  | PrintTypeClasses -> msg_notice (Prettyp.print_typeclasses())
  | PrintInstances c -> msg_notice (Prettyp.print_instances (smart_global c))
  | PrintLtac qid -> msg_notice (Tacintern.print_ltac (snd (qualid_of_reference qid)))
  | PrintCoercions -> msg_notice (Prettyp.print_coercions())
  | PrintCoercionPaths (cls,clt) ->
      msg_notice (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintCanonicalConversions -> msg_notice (Prettyp.print_canonical_projections ())
  | PrintUniverses (b, None) ->
    let univ = Global.universes () in
    let univ = if b then Univ.sort_universes univ else univ in
    msg_notice (Univ.pr_universes univ)
  | PrintUniverses (b, Some s) -> dump_universes b s
  | PrintHint r -> msg_notice (Auto.pr_hint_ref (smart_global r))
  | PrintHintGoal -> msg_notice (Auto.pr_applicable_hint ())
  | PrintHintDbName s -> msg_notice (Auto.pr_hint_db_by_name s)
  | PrintRewriteHintDbName s -> msg_notice (Autorewrite.print_rewrite_hintdb s)
  | PrintHintDb -> msg_notice (Auto.pr_searchtable ())
  | PrintScopes ->
      msg_notice (Notation.pr_scopes (Constrextern.without_symbols pr_lglob_constr))
  | PrintScope s ->
      msg_notice (Notation.pr_scope (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintVisibility s ->
      msg_notice (Notation.pr_visibility (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintAbout qid ->
    msg_notice (print_about qid)
  | PrintImplicit qid ->
    dump_global qid; msg_notice (print_impargs qid)
  | PrintAssumptions (o,t,r) ->
      (* Prints all the axioms and section variables used by a term *)
      let cstr = printable_constr_of_global (smart_global r) in
      let st = Conv_oracle.get_transp_state () in
      let nassums =
	Assumptions.assumptions st ~add_opaque:o ~add_transparent:t cstr in
      msg_notice (Printer.pr_assumptionset (Global.env ()) nassums)

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found ->
    user_err_loc (loc, "global_module",
      str "Module/section " ++ pr_qualid qid ++ str " not found.")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let interp_search_about_item = function
  | SearchSubPattern pat ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) pat in
      GlobSearchSubPattern pat
  | SearchString (s,None) when Id.is_valid s ->
      GlobSearchString s
  | SearchString (s,sc) ->
      try
	let ref =
	  Notation.interp_notation_as_global_reference Loc.ghost
	    (fun _ -> true) s sc in
	GlobSearchSubPattern (Pattern.PRef ref)
      with UserError _ ->
	error ("Unable to interp \""^s^"\" either as a reference or \
          	as an identifier component")

let vernac_search s r =
  let r = interp_search_restriction r in
  let env = Global.env () in
  let get_pattern c = snd (Constrintern.intern_constr_pattern Evd.empty env c) in
  match s with
  | SearchPattern c ->
      msg_notice (Search.search_pattern (get_pattern c) r)
  | SearchRewrite c ->
      msg_notice (Search.search_rewrite (get_pattern c) r)
  | SearchHead c ->
      msg_notice (Search.search_by_head (get_pattern c) r)
  | SearchAbout sl ->
      msg_notice (Search.search_about (List.map (on_snd interp_search_about_item) sl) r)

let vernac_locate = function
  | LocateTerm (AN qid) -> msg_notice (print_located_qualid qid)
  | LocateTerm (ByNotation (_,ntn,sc)) ->
      msg_notice
        (Notation.locate_notation
          (Constrextern.without_symbols pr_lglob_constr) ntn sc)
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> print_located_module qid
  | LocateTactic qid -> print_located_tactic qid
  | LocateFile f -> msg_notice (locate_file f)

(****************)
(* Backtracking *)

(** NB: these commands are now forbidden in non-interactive use,
    e.g. inside VernacLoad, VernacList, ... *)

let vernac_backto lbl =
  try
    let lbl' = Backtrack.backto lbl in
    if not (Int.equal lbl lbl') then
      Pp.msg_warning
	(str "Actually back to state "++ Pp.int lbl' ++ str ".");
    try_print_subgoals ()
  with Backtrack.Invalid -> error "Invalid backtrack."

let vernac_back n =
  try
    let extra = Backtrack.back n in
    if not (Int.equal extra 0) then
      Pp.msg_warning
	(str "Actually back by " ++ Pp.int (extra+n) ++ str " steps.");
    try_print_subgoals ()
  with Backtrack.Invalid -> error "Invalid backtrack."

let vernac_reset_name id =
  try
    let globalized =
      try
	let gr = Smartlocate.global_with_alias (Ident id) in
	Dumpglob.add_glob (fst id) gr;
	true
      with e when Errors.noncritical e -> false in

    if not globalized then begin
       try begin match Lib.find_opening_node (snd id) with
          | Lib.OpenedSection _ -> Dumpglob.dump_reference (fst id)
              (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
          (* Might be nice to implement module cases, too.... *)
          | _ -> ()
       end with UserError _ -> ()
    end;

    if Backtrack.is_active () then
      (Backtrack.reset_name id; try_print_subgoals ())
    else
      (* When compiling files, Reset is now allowed again
	 as asked by A. Chlipala. we emulate a simple reset,
	 that discards all proofs. *)
      let lbl = Lib.label_before_name id in
      Pfedit.delete_all_proofs ();
      Pp.msg_warning (str "Reset command occurred in non-interactive mode.");
      Lib.reset_label lbl
  with Backtrack.Invalid | Not_found -> error "Invalid Reset."


let vernac_reset_initial () =
  if Backtrack.is_active () then
    Backtrack.reset_initial ()
  else begin
    Pp.msg_warning (str "Reset command occurred in non-interactive mode.");
    Lib.raw_reset_initial ()
  end

(* For compatibility with ProofGeneral: *)

let vernac_backtrack snum pnum naborts =
  Backtrack.backtrack snum pnum naborts;
  try_print_subgoals ()


(********************)
(* Proof management *)

let vernac_abort = function
  | None ->
      Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
      delete_current_proof ();
      if_verbose msg_info (str "Current goal aborted")
  | Some id ->
      Backtrack.mark_unreachable [snd id];
      delete_proof id;
      let s = Id.to_string (snd id) in
      if_verbose msg_info (str ("Goal "^s^" aborted"))

let vernac_abort_all () =
  if refining() then begin
    Backtrack.mark_unreachable (Pfedit.get_all_proof_names ());
    delete_all_proofs ();
    msg_info (str "Current goals aborted")
  end else
    error "No proof-editing in progress."

let vernac_restart () =
  Backtrack.mark_unreachable [Pfedit.get_current_proof_name ()];
  restart_proof(); print_subgoals ()

let vernac_undo n =
  let d = Pfedit.current_proof_depth () - n in
  Backtrack.mark_unreachable ~after:d [Pfedit.get_current_proof_name ()];
  Pfedit.undo n; print_subgoals ()

let vernac_undoto n =
  Backtrack.mark_unreachable ~after:n [Pfedit.get_current_proof_name ()];
  Pfedit.undo_todepth n;
  print_subgoals ()

let vernac_focus gln =
  let p = Proof_global.give_me_the_proof () in
  let n = match gln with None -> 1 | Some n -> n in
  if Int.equal n 0 then
    Errors.error "Invalid goal number: 0. Goal numbering starts with 1."
  else
    try Proof.focus focus_command_cond () n p; print_subgoals ()
    with Proofview.IndexOutOfRange ->
      Errors.error "No such unproven subgoal."

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus () =
  let p = Proof_global.give_me_the_proof () in
  Proof.unfocus command_focus p; print_subgoals ()

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused () =
  let p = Proof_global.give_me_the_proof () in
  if Proof.unfocused p then
    msg_notice (str"The proof is indeed fully unfocused.")
  else
    error "The proof is not fully unfocused."


(* BeginSubproof / EndSubproof. 
    BeginSubproof (vernac_subproof) focuses on the first goal, or the goal
    given as argument.
    EndSubproof (vernac_end_subproof) unfocuses from a BeginSubproof, provided
    that the proof of the goal has been completed.
*)
let subproof_kind = Proof.new_focus_kind ()
let subproof_cond = Proof.done_cond subproof_kind

let vernac_subproof gln =
  let p = Proof_global.give_me_the_proof () in
  begin match gln with
  | None -> Proof.focus subproof_cond () 1 p
  | Some n -> Proof.focus subproof_cond () n p
  end ;
  print_subgoals ()

let vernac_end_subproof () =
  let p = Proof_global.give_me_the_proof () in
  Proof.unfocus subproof_kind p ; print_subgoals ()


let vernac_bullet (bullet:Proof_global.Bullet.t) =
  let p = Proof_global.give_me_the_proof () in
  Proof.transaction p 
    (fun () -> Proof_global.Bullet.put p bullet);
  (* Makes the focus visible in emacs by re-printing the goal. *)
  if !Flags.print_emacs then print_subgoals ()


let vernac_show = function
  | ShowGoal goalref ->
    let info = match goalref with
      | OpenSubgoals -> pr_open_subgoals ()
      | NthGoal n -> pr_nth_open_subgoal n
      | GoalId id -> pr_goal_by_id id
    in
    msg_notice info
  | ShowGoalImplicitly None ->
      Constrextern.with_implicits msg_notice (pr_open_subgoals ())
  | ShowGoalImplicitly (Some n) ->
      Constrextern.with_implicits msg_notice (pr_nth_open_subgoal n)
  | ShowProof -> show_proof ()
  | ShowNode -> show_node ()
  | ShowScript -> show_script ()
  | ShowExistentials -> show_top_evars ()
  | ShowTree -> show_prooftree ()
  | ShowProofNames ->
      msg_notice (pr_sequence pr_id (Pfedit.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ShowMatch id -> show_match id
  | ShowThesis -> show_thesis ()


let vernac_check_guard () =
  let pts = get_pftreestate () in
  let pfterm = List.hd (Proof.partial_proof pts) in
  let message =
    try
      let { Evd.it=gl ; sigma=sigma } = Proof.V82.top_goal pts in
      Inductiveops.control_only_guard (Goal.V82.env sigma gl)
	pfterm;
      (str "The condition holds up to here")
    with UserError(_,s) ->
      (str ("Condition violated: ") ++s)
  in
  msg_notice message

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * "poly" is the prefix "Polymorphic" or "Monomorphic" *)
let interp locality poly c = match c with
  (* Control (done in vernac) *)
  | (VernacTime _|VernacList _|VernacLoad _|VernacTimeout _|VernacFail _) ->
      assert false

  (* Syntax *)
  | VernacTacticNotation (n,r,e) ->
      Metasyntax.add_tactic_notation (make_module_locality locality,n,r,e)
  | VernacSyntaxExtension (local,sl) ->
      vernac_syntax_extension locality local sl
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacBindScope (sc,rl) -> vernac_bind_scope sc rl
  | VernacOpenCloseScope (local, s) -> vernac_open_close_scope locality local s
  | VernacArgumentsScope (qid,scl) -> vernac_arguments_scope locality qid scl
  | VernacInfix (local,mv,qid,sc) -> vernac_infix locality local mv qid sc
  | VernacNotation (local,c,infpl,sc) ->
      vernac_notation locality local c infpl sc

  (* Gallina *)
  | VernacDefinition (k,lid,d) -> vernac_definition locality poly k lid d
  | VernacStartTheoremProof (k,l,top) -> vernac_start_proof poly k l top
  | VernacEndProof e -> vernac_end_proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,nl,l) -> vernac_assumption locality poly stre l nl
  | VernacInductive (finite,infer,l) -> vernac_inductive poly finite infer l
  | VernacFixpoint (local, l) -> vernac_fixpoint locality poly local l
  | VernacCoFixpoint (local, l) -> vernac_cofixpoint locality poly local l
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l

  (* Modules *)
  | VernacDeclareModule (export,lid,bl,mtyo) ->
      vernac_declare_module export lid bl mtyo
  | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
      vernac_define_module export lid bl mtys mexprl
  | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
      vernac_declare_module_type lid bl mtys mtyo
  | VernacInclude in_asts ->
      vernac_include in_asts
  (* Gallina extensions *)
  | VernacBeginSection lid -> vernac_begin_section lid

  | VernacEndSegment lid -> vernac_end_segment lid

  | VernacRequire (export, qidl) -> vernac_require export qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (local,r,s,t) -> vernac_coercion locality poly local r s t
  | VernacIdentityCoercion (local,(_,id),s,t) ->
      vernac_identity_coercion locality poly local id s t

  (* Type classes *)
  | VernacInstance (abst, sup, inst, props, pri) ->
      vernac_instance abst locality poly sup inst props pri
  | VernacContext sup -> vernac_context sup
  | VernacDeclareInstances ids -> vernac_declare_instances locality ids
  | VernacDeclareClass id -> vernac_declare_class id

  (* Solving *)
  | VernacSolve (n,tac,b) -> vernac_solve n tac b
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp, f) -> vernac_require_from exp f
  | VernacAddLoadPath (isrec,s,alias) -> vernac_add_loadpath isrec s alias
  | VernacRemoveLoadPath s -> vernac_remove_loadpath s
  | VernacAddMLPath (isrec,s) -> vernac_add_ml_path isrec s
  | VernacDeclareMLModule l -> vernac_declare_ml_module locality l
  | VernacChdir s -> vernac_chdir s

  (* State management *)
  | VernacWriteState s -> vernac_write_state s
  | VernacRestoreState s -> vernac_restore_state s

  (* Resetting *)
  | VernacResetName id -> vernac_reset_name id
  | VernacResetInitial -> vernac_reset_initial ()
  | VernacBack n -> vernac_back n
  | VernacBackTo n -> vernac_backto n

  (* Commands *)
  | VernacDeclareTacticDefinition def ->
      vernac_declare_tactic_definition locality def
  | VernacCreateHintDb (dbname,b) -> vernac_create_hintdb locality dbname b
  | VernacRemoveHints (dbnames,ids) -> vernac_remove_hints locality dbnames ids
  | VernacHints (local,dbnames,hints) ->
      vernac_hints locality poly local dbnames hints
  | VernacSyntacticDefinition (id,c,local,b) ->
      vernac_syntactic_definition locality  id c local b
  | VernacDeclareImplicits (qid,l) ->
      vernac_declare_implicits locality qid l
  | VernacArguments (qid, l, narg, flags) ->
      vernac_declare_arguments locality qid l narg flags 
  | VernacReserve bl -> vernac_reserve bl
  | VernacGeneralizable gen -> vernac_generalizable locality gen
  | VernacSetOpacity qidl -> vernac_set_opacity locality qidl
  | VernacSetStrategy l -> vernac_set_strategy locality l
  | VernacSetOption (key,v) -> vernac_set_option locality key v
  | VernacUnsetOption key -> vernac_unset_option locality key
  | VernacRemoveOption (key,v) -> vernac_remove_option key v
  | VernacAddOption (key,v) -> vernac_add_option key v
  | VernacMemOption (key,v) -> vernac_mem_option key v
  | VernacPrintOption key -> vernac_print_option key
  | VernacCheckMayEval (r,g,c) -> vernac_check_may_eval r g c
  | VernacDeclareReduction (s,r) -> vernac_declare_reduction locality s r
  | VernacGlobalCheck c -> vernac_global_check c
  | VernacPrint p -> vernac_print p
  | VernacSearch (s,r) -> vernac_search s r
  | VernacLocate l -> vernac_locate l
  | VernacComments l -> if_verbose msg_info (str "Comments ok\n")
  | VernacNop -> ()

  (* Proof management *)
  | VernacGoal t -> vernac_start_proof poly Theorem [None,([],t,None)] false
  | VernacAbort id -> vernac_abort id
  | VernacAbortAll -> vernac_abort_all ()
  | VernacRestart -> vernac_restart ()
  | VernacUndo n -> vernac_undo n
  | VernacUndoTo n -> vernac_undoto n
  | VernacBacktrack (snum,pnum,naborts) -> vernac_backtrack snum pnum naborts
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacUnfocused -> vernac_unfocused ()
  | VernacBullet b -> vernac_bullet b
  | VernacSubproof n -> vernac_subproof n
  | VernacEndSubproof -> vernac_end_subproof ()
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacProof (None, None) -> print_subgoals ()
  | VernacProof (Some tac, None) -> vernac_set_end_tac tac ; print_subgoals ()
  | VernacProof (None, Some l) -> vernac_set_used_variables l ; print_subgoals ()
  | VernacProof (Some tac, Some l) -> 
      vernac_set_end_tac tac; vernac_set_used_variables l ; print_subgoals ()
  | VernacProofMode mn -> Proof_global.set_proof_mode mn
  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Extensions *)
  | VernacExtend (opn,args) -> Vernacinterp.call ?locality (opn,args)

  (* Handled elsewhere *)
  | VernacProgram _
  | VernacPolymorphic _
  | VernacLocal _ -> assert false

(* Vernaculars that take a locality flag *)
let check_vernac_supports_locality c l =
  match l, c with
  | None, _ -> ()
  | Some _, (
      VernacTacticNotation _
    | VernacOpenCloseScope _
    | VernacSyntaxExtension _ | VernacInfix _ | VernacNotation _
    | VernacDefinition _ | VernacFixpoint _ | VernacCoFixpoint _
    | VernacAssumption _
    | VernacCoercion _ | VernacIdentityCoercion _
    | VernacInstance _ | VernacDeclareInstances _
    | VernacDeclareMLModule _
    | VernacDeclareTacticDefinition _
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacSyntacticDefinition _
    | VernacArgumentsScope _ | VernacDeclareImplicits _ | VernacArguments _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacSetOption _ | VernacUnsetOption _
    | VernacDeclareReduction _
    | VernacExtend _ ) -> ()
  | Some _, _ -> Errors.error "This command does not support Locality"

(* Vernaculars that take a polymorphism flag *)
let check_vernac_supports_polymorphism c p =
  match p, c with
  | None, _ -> ()
  | Some _, (
      VernacDefinition _ | VernacFixpoint _ | VernacCoFixpoint _
    | VernacAssumption _ | VernacInductive _ 
    | VernacStartTheoremProof _
    | VernacCoercion _ | VernacIdentityCoercion _
    | VernacInstance _ | VernacDeclareInstances _
    | VernacHints _
    | VernacExtend _ ) -> ()
  | Some _, _ -> Errors.error "This command does not support Polymorphism"

let enforce_polymorphism = function
  | None -> Flags.is_universe_polymorphism ()
  | Some b -> b

let interp c =
  let orig_program_mode = Flags.is_program_mode () in
  let rec aux ?locality ?polymorphism isprogcmd = function
    | VernacProgram c when not isprogcmd -> aux ?locality ?polymorphism true c
    | VernacProgram _ -> Errors.error "Program mode specified twice"
    | VernacPolymorphic (b, c) when polymorphism = None -> 
      aux ?locality ~polymorphism:b isprogcmd c
    | VernacPolymorphic (b, c) -> Errors.error "Polymorphism specified twice"
    | VernacLocal (b, c) when locality = None -> 
      aux ~locality:b ?polymorphism isprogcmd c
    | VernacLocal _ -> Errors.error "Locality specified twice"
    | c -> 
        check_vernac_supports_locality c locality;
        check_vernac_supports_polymorphism c polymorphism;
	let poly = enforce_polymorphism polymorphism in
        Obligations.set_program_mode isprogcmd;
        try
          interp locality poly c;
          if orig_program_mode || not !Flags.program_mode || isprogcmd then
            Flags.program_mode := orig_program_mode
        with
          | reraise ->
            let e = Errors.push reraise in
            Flags.program_mode := orig_program_mode;
            raise e
  in
    aux false c
