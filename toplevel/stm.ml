(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let prerr_endline s = if !Flags.debug then prerr_endline s else ()

open Vernacexpr
open Errors
open Pp
open Names
open Util
open Ppvernac
open Vernac_classifier

(* During interactive use we cache more states so that Undoing is fast *)
let interactive () =
  if !Flags.ide_slave || !Flags.print_emacs || not !Flags.batch_mode then `Yes
  else `No

let fallback_to_lazy_if_marshal_error = ref true
let fallback_to_lazy_if_slave_dies = ref true
let coq_slave_extra_env = ref [||]

(* Wrapper for Vernacentries.interp to set the feedback id *)
let vernac_interp ?proof id (verbosely, loc, expr) =
  let internal_command = function
    | VernacResetName _ | VernacResetInitial | VernacBack _
    | VernacBackTo _ | VernacRestart | VernacUndo _ | VernacUndoTo _
    | VernacBacktrack _ | VernacAbortAll | VernacAbort _ -> true | _ -> false in
  if internal_command expr then begin
    prerr_endline ("ignoring " ^ string_of_ppcmds(pr_vernac expr))
  end else begin
    Pp.set_id_for_feedback (Interface.State id);
    prerr_endline ("interpreting " ^ string_of_ppcmds(pr_vernac expr));
    try Vernacentries.interp ~verbosely ?proof (loc, expr)
    with e -> raise (Errors.push (Cerrors.process_vernac_interp_error e))
  end

(* Wrapper for Vernac.parse_sentence to set the feedback id *)
let vernac_parse eid s =
  set_id_for_feedback (Interface.Edit eid);
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  Flags.with_option Flags.we_are_parsing (fun () ->
    match Pcoq.Gram.entry_parse Pcoq.main_entry pa with
    | None -> raise (Invalid_argument "vernac_parse")
    | Some ast -> ast)
  ()

type ast = bool * Loc.t * vernac_expr
let pr_ast (_, _, v) = pr_vernac v

module Vcs_ = Vcs.Make(Stateid)
type future_proof = Proof_global.closed_proof_output Future.computation
type proof_mode = string
type depth = int
type branch_type =
  [ `Master
  | `Proof of proof_mode * depth
  | `Edit of proof_mode * Stateid.t * Stateid.t ]
type cmd_t = ast * Id.t list
type fork_t = ast * Vcs_.Branch.t * Id.t list * Decl_kinds.polymorphic
type qed_t = {
  qast : ast;
  keep : vernac_qed_type;
  mutable fproof : future_proof option;
  brname : Vcs_.Branch.t;
  brinfo : branch_type Vcs_.branch_info
}
type seff_t = ast option
type alias_t = Stateid.t
type transaction =
  | Cmd    of cmd_t
  | Fork   of fork_t
  | Qed    of qed_t
  | Sideff of seff_t
  | Alias  of alias_t
  | Noop
type step =
  [ `Cmd    of cmd_t
  | `Fork   of fork_t
  | `Qed    of qed_t * Stateid.t
  | `Sideff of [ `Ast of ast * Stateid.t | `Id of Stateid.t ]
  | `Alias  of alias_t ]
type visit = { step : step; next : Stateid.t }

type state = {
  system : States.state;
  proof : Proof_global.state;
  shallow : bool
}
type branch = Vcs_.Branch.t * branch_type Vcs_.branch_info
type backup = { mine : branch; others : branch list }
type 'vcs state_info = { (* Make private *)
  mutable n_reached : int;
  mutable n_goals : int;
  mutable state : state option;
  mutable vcs_backup : 'vcs option * backup option;
}
let default_info () =
  { n_reached = 0; n_goals = 0; state = None; vcs_backup = None,None }

(* Functions that work on a Vcs with a specific branch type *)
module Vcs_aux : sig

  val proof_nesting : (branch_type, 't,'i) Vcs_.t -> int
  val find_proof_at_depth :
    (branch_type, 't, 'i) Vcs_.t -> int ->
      Vcs_.Branch.t * branch_type Vcs_.branch_info
  exception Expired
  val visit : (branch_type, transaction,'i) Vcs_.t -> Vcs_.Dag.node -> visit

end = struct (* {{{ *)

  let proof_nesting vcs =
    List.fold_left max 0
      (List.map_filter
        (function
         | { Vcs_.kind = `Proof (_,n) } -> Some n
         | { Vcs_.kind = `Edit _ } -> Some 1
         | _ -> None)
        (List.map (Vcs_.get_branch vcs) (Vcs_.branches vcs)))

  let find_proof_at_depth vcs pl =
    try List.find (function
          | _, { Vcs_.kind = `Proof(m, n) } -> Int.equal n pl
          | _, { Vcs_.kind = `Edit _ } -> anomaly(str"find_proof_at_depth")
          | _ -> false)
        (List.map (fun h -> h, Vcs_.get_branch vcs h) (Vcs_.branches vcs))
    with Not_found -> failwith "find_proof_at_depth"

  exception Expired
  let visit vcs id =
    if Stateid.equal id Stateid.initial then
      anomaly(str"Visiting the initial state id")
    else if Stateid.equal id Stateid.dummy then
      anomaly(str"Visiting the dummy state id")
    else
    try
      match Vcs_.Dag.from_node (Vcs_.dag vcs) id with
      | [n, Cmd x] -> { step = `Cmd x; next = n }
      | [n, Alias x] -> { step = `Alias x; next = n }
      | [n, Fork x] -> { step = `Fork x; next = n }
      | [n, Qed x; p, Noop]
      | [p, Noop; n, Qed x] -> { step = `Qed (x,p); next = n }
      | [n, Sideff None; p, Noop]
      | [p, Noop; n, Sideff None]-> { step = `Sideff (`Id p); next = n }
      | [n, Sideff (Some x); p, Noop]
      | [p, Noop; n, Sideff (Some x)]-> { step = `Sideff(`Ast (x,p)); next = n }
      | [n, Sideff (Some x)]-> {step = `Sideff(`Ast (x,Stateid.dummy)); next=n}
      | _ -> anomaly (str ("Malformed VCS at node "^Stateid.to_string id))
    with Not_found -> raise Expired

end (* }}} *)

(* Imperative wrap around VCS to obtain _the_ VCS *)
module VCS : sig

  exception Expired

  module Branch : (module type of Vcs_.Branch with type t = Vcs_.Branch.t)
  type id = Stateid.t
  type 'branch_type branch_info = 'branch_type Vcs_.branch_info = {
    kind : [> `Master] as 'branch_type;
    root : id;
    pos  : id;
  }

  type vcs = (branch_type, transaction, vcs state_info) Vcs_.t

  val init : id -> unit

  val current_branch : unit -> Branch.t
  val checkout : Branch.t -> unit
  val branches : unit -> Branch.t list
  val get_branch : Branch.t -> branch_type branch_info
  val get_branch_pos : Branch.t -> id
  val new_node : unit -> id
  val merge : id -> ours:transaction -> ?into:Branch.t -> Branch.t -> unit
  val rewrite_merge : id -> ours:transaction -> at:id -> Branch.t -> unit
  val delete_branch : Branch.t -> unit
  val commit : id -> transaction -> unit
  val mk_branch_name : ast -> Branch.t
  val edit_branch : Branch.t
  val branch : ?root:id -> ?pos:id -> Branch.t -> branch_type -> unit
  val reset_branch : Branch.t -> id -> unit
  val reachable : id -> Vcs_.NodeSet.t
  val cur_tip : unit -> id

  val get_info : id -> vcs state_info
  val reached : id -> bool -> unit
  val goals : id -> int -> unit
  val set_state : id -> state -> unit
  val forget_state : id -> unit

  (* TODO: move elsewhere if possible, so that purify can be just called *)
  (* cuts from start -> stop, raising Expired if some nodes are not there *)
  val slice : start:id -> stop:id -> purify:(state -> state) -> vcs
  
  val create_cluster : id list -> tip:id -> unit
  val cluster_of : id -> id option
  val delete_cluster_of : id -> unit

  val proof_nesting : unit -> int
  val checkout_shallowest_proof_branch : unit -> unit
  val propagate_sideff : ast option -> unit

  val gc : unit -> unit

  val visit : id -> visit

  val print : ?now:bool -> unit -> unit

  val backup : unit -> vcs
  val restore : vcs -> unit

end = struct (* {{{ *)

  include Vcs_
  exception Expired = Vcs_aux.Expired

  module StateidSet = Set.Make(Stateid)
  open Printf

  let print_dag vcs () = (* {{{ *)
    let fname = "stm" ^ string_of_int (max 0 !Flags.coq_slave_mode) in
    let string_of_transaction = function
      | Cmd (t, _) | Fork (t, _, _, _) ->
          (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff (Some t) ->
          sprintf "Sideff(%s)"
            (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff None -> "EnvChange"
      | Noop -> " "
      | Alias id -> sprintf "Alias(%s)" (Stateid.to_string id)
      | Qed { qast } -> string_of_ppcmds (pr_ast qast) in
    let is_green id = 
      match get_info vcs id with
      | Some { state = Some _ } -> true
      | _ -> false in
    let is_red id =
      match get_info vcs id with
      | Some s -> Int.equal s.n_reached ~-1
      | _ -> false in
    let head = current_branch vcs in
    let heads =
      List.map (fun x -> x, (get_branch vcs x).pos) (branches vcs) in
    let graph = dag vcs in
    let quote s =
      Str.global_replace (Str.regexp "\n") "<BR/>"
       (Str.global_replace (Str.regexp "<") "&lt;"
        (Str.global_replace (Str.regexp ">") "&gt;"
         (Str.global_replace (Str.regexp "\"") "&quot;"
          (Str.global_replace (Str.regexp "&") "&amp;"
           (String.sub s 0 (min (String.length s) 20)))))) in
    let fname_dot, fname_ps =
      let f = "/tmp/" ^ Filename.basename fname in
      f ^ ".dot", f ^ ".pdf" in
    let node id = "s" ^ Stateid.to_string id in
    let edge tr =
      sprintf "<<FONT POINT-SIZE=\"12\" FACE=\"sans\">%s</FONT>>"
        (quote (string_of_transaction tr)) in
    let ids = ref StateidSet.empty in
    let clus = Hashtbl.create 13 in
    let node_info id =
      match get_info vcs id with
      | None -> ""
      | Some info ->
          sprintf "<<FONT POINT-SIZE=\"12\">%s</FONT>" (Stateid.to_string id) ^
          sprintf " <FONT POINT-SIZE=\"11\">r:%d g:%d</FONT>>"
            info.n_reached info.n_goals in
    let color id =
      if is_red id then "red" else if is_green id then "green" else "white" in
    let nodefmt oc id =
      fprintf oc "%s [label=%s,style=filled,fillcolor=%s];\n"
        (node id) (node_info id) (color id) in
    let add_to_clus_or_ids from cf =
      match cf with
      | None -> ids := StateidSet.add from !ids; false
      | Some c -> Hashtbl.replace clus c
         (try let n = Hashtbl.find clus c in from::n
         with Not_found -> [from]); true in
    let oc = open_out fname_dot in
    output_string oc "digraph states {\nsplines=ortho\n";
    Dag.iter graph (fun from cf _ l ->
      let c1 = add_to_clus_or_ids from cf in
      List.iter (fun (dest, trans) ->
       let c2 = add_to_clus_or_ids dest (Dag.cluster_of graph dest) in
       fprintf oc "%s -> %s [label=%s,labelfloat=%b];\n"
           (node from) (node dest) (edge trans) (c1 && c2)) l
    );
    StateidSet.iter (nodefmt oc) !ids;
    Hashtbl.iter (fun c nodes ->
       fprintf oc "subgraph cluster_%s {\n" (Dag.Cluster.to_string c);
       List.iter (nodefmt oc) nodes;
       fprintf oc "color=blue; }\n"
    ) clus;
    List.iteri (fun i (b,id) ->
      let shape = if Branch.equal head b then "box3d" else "box" in
      fprintf oc "b%d -> %s;\n" i (node id);
      fprintf oc "b%d [shape=%s,label=\"%s\"];\n" i shape
        (Branch.to_string b);
    ) heads;
    output_string oc "}\n";
    close_out oc;
    ignore(Sys.command
      ("dot -Tpdf -Gcharset=latin1 " ^ fname_dot ^ " -o" ^ fname_ps))
  (* }}} *)
  
  type vcs = (branch_type, transaction, vcs state_info) t
  let vcs : vcs ref = ref (empty Stateid.dummy)

  let init id =
    vcs := empty id;
    vcs := set_info !vcs id (default_info ())

  let current_branch () = current_branch !vcs

  let checkout head = vcs := checkout !vcs head
  let master = Branch.master
  let branches () = branches !vcs
  let get_branch head = get_branch !vcs head
  let get_branch_pos head = (get_branch head).pos
  let new_node () =
    let id = Stateid.fresh () in
    vcs := set_info !vcs id (default_info ());
    id
  let merge id ~ours ?into branch =
    vcs := merge !vcs id ~ours ~theirs:Noop ?into branch
  let delete_branch branch = vcs := delete_branch !vcs branch
  let reset_branch branch id = vcs := reset_branch !vcs branch id
  let commit id t = vcs := commit !vcs id t
  let rewrite_merge id ~ours ~at branch =
    vcs := rewrite_merge !vcs id ~ours ~theirs:Noop ~at branch
  let reachable id = reachable !vcs id
  let mk_branch_name (_, _, x) = Branch.make
    (match x with
    | VernacDefinition (_,(_,i),_) -> string_of_id i
    | VernacStartTheoremProof (_,[Some (_,i),_],_) -> string_of_id i
    | _ -> "branch")
  let edit_branch = Branch.make "edit"
  let branch ?root ?pos name kind = vcs := branch !vcs ?root ?pos name kind
  let get_info id =
    match get_info !vcs id with
    | Some x -> x
    | None -> raise Vcs_aux.Expired
  let set_state id s = (get_info id).state <- Some s
  let forget_state id = (get_info id).state <- None
  let reached id b =
    let info = get_info id in
    if b then info.n_reached <- info.n_reached + 1
    else info.n_reached <- -1
  let goals id n = (get_info id).n_goals <- n
  let cur_tip () = get_branch_pos (current_branch ())

  let proof_nesting () = Vcs_aux.proof_nesting !vcs

  let checkout_shallowest_proof_branch () =
    if List.mem edit_branch (Vcs_.branches !vcs) then begin
      checkout edit_branch;
      match get_branch edit_branch with
      | { kind = `Edit (mode, _, _) } -> Proof_global.activate_proof_mode mode
      | _ -> assert false
    end else
      let pl = proof_nesting () in
      try
        let branch, mode = match Vcs_aux.find_proof_at_depth !vcs pl with
          | h, { Vcs_.kind = `Proof (m, _) } -> h, m | _ -> assert false in
        checkout branch;
        prerr_endline ("mode:" ^ mode);
        Proof_global.activate_proof_mode mode
      with Failure _ ->
        checkout Branch.master;
        Proof_global.disactivate_proof_mode "Classic"

  (* copies the transaction on every open branch *)
  let propagate_sideff t =
    List.iter (fun b ->
      checkout b;
      let id = new_node () in
      merge id ~ours:(Sideff t) ~into:b Branch.master)
    (List.filter (fun b -> not (Branch.equal b Branch.master)) (branches ()))
  
  let visit id = Vcs_aux.visit !vcs id

  let slice ~start ~stop ~purify =
    let l =
      let rec aux id =
        if Stateid.equal id stop then [] else
        match visit id with
        | { next = n; step = `Cmd x } -> (id,Cmd x) :: aux n
        | { next = n; step = `Alias x } -> (id,Alias x) :: aux n
        | { next = n; step = `Sideff (`Ast (x,_)) } ->
             (id,Sideff (Some x)) :: aux n
        | _ -> anomaly(str("Cannot slice from "^ Stateid.to_string start ^
                           " to "^Stateid.to_string stop))
      in aux start in
    let v = Vcs_.empty stop in
    let info = get_info stop in
    (* Stm should have reached the beginning of proof *)
    assert (not (Option.is_empty info.state));
    (* This may be expensive *)
    let info = { info with
      state = Some (purify (Option.get info.state));
      vcs_backup = None,None } in
    let v = Vcs_.set_info v stop info in
    List.fold_right (fun (id,tr) v ->
      let v = Vcs_.commit v id tr in
      let info = get_info id in
      (* TODO: we could drop all of them but for the last one and purify it,
       * so that proofs partially executed in the main process are not
       * completely re-executed in the slave process *)
      let info = { info with state = None; vcs_backup = None,None } in
      let v = Vcs_.set_info v id info in
      v) l v

  let create_cluster l ~tip = vcs := create_cluster !vcs l tip
  let cluster_of id = Option.map Dag.Cluster.data (cluster_of !vcs id)
  let delete_cluster_of id =
    Option.iter (fun x -> vcs := delete_cluster !vcs x) (Vcs_.cluster_of !vcs id)

  let gc () = vcs := gc !vcs

  module NB : sig (* Non blocking Sys.command *)

    val command : now:bool -> (unit -> unit) -> unit

  end = struct (* {{{ *)
    
    let m = Mutex.create ()
    let c = Condition.create ()
    let job = ref None
    let worker = ref None

    let set_last_job j =
      Mutex.lock m;
      job := Some j;
      Condition.signal c;
      Mutex.unlock m

    let get_last_job () =
      Mutex.lock m;
      while Option.is_empty !job do Condition.wait c m; done;
      match !job with
      | None -> assert false
      | Some x -> job := None; Mutex.unlock m; x

    let run_command () =
      try while true do get_last_job () () done
      with e -> () (* No failure *)

    let command ~now job =
      if now then job ()
      else begin
        set_last_job job;
        if Option.is_empty !worker then
          worker := Some (Thread.create run_command ())
      end

  end (* }}} *)

  let print ?(now=false) () =
    if not !Flags.debug && not now then () else NB.command ~now (print_dag !vcs)

  let backup () = !vcs
  let restore v = vcs := v

end (* }}} *)

(* Fills in the nodes of the VCS *)
module State : sig
  
  (** The function is from unit, so it uses the current state to define
      a new one.  I.e. one may been to install the right state before
      defining a new one.
      Warning: an optimization in installed_cached requires that state
      modifying functions are always executed using this wrapper. *)
  val define :
    ?redefine:bool -> ?cache:Summary.marshallable -> (unit -> unit) -> Stateid.t -> unit

  val install_cached : Stateid.t -> unit
  val is_cached : Stateid.t -> bool

  val exn_on : Stateid.t -> ?valid:Stateid.t -> exn -> exn

  (* projects a state so that it can be marshalled and its content is
   * sufficient for the execution of Coq on a proof branch *)
  val make_shallow : state -> state

end = struct (* {{{ *)

  (* cur_id holds Stateid.dummy in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref Stateid.dummy

  (* helpers *)
  let freeze_global_state marshallable =
    { system = States.freeze ~marshallable;
      proof = Proof_global.freeze ~marshallable;
      shallow = (marshallable = `Shallow) }
  let unfreeze_global_state { system; proof } =
    States.unfreeze system; Proof_global.unfreeze proof

  (* hack to make futures functional *)
  let in_t, out_t = Dyn.create "state4future"
  let () = Future.set_freeze
    (fun () -> in_t (freeze_global_state `No, !cur_id))
    (fun t -> let s,i = out_t t in unfreeze_global_state s; cur_id := i)

  let make_shallow s =
    if s.shallow then s
    else
      Future.purify (fun s ->
        Printf.eprintf
          "make_shallow & define should be protected by a lock!\n";
        unfreeze_global_state s;
        freeze_global_state `Shallow) s

  let is_cached id =
    Stateid.equal id !cur_id ||
    match VCS.get_info id with
    | { state = Some _ } -> true
    | _ -> false

  let install_cached id =
    if Stateid.equal id !cur_id then () else (* optimization *)
    let s =
      match VCS.get_info id with
      | { state = Some s } -> s
      | _ -> anomaly (str "unfreezing a non existing state") in
    unfreeze_global_state s; cur_id := id

  let freeze marhallable id = VCS.set_state id (freeze_global_state marhallable)

  let exn_on id ?valid e =
    let loc = Option.default Loc.ghost (Loc.get_loc e) in
    let msg = string_of_ppcmds (print e) in
    Pp.feedback ~state_id:id (Interface.ErrorMsg (loc, msg));
    Stateid.add e ?valid id

  let define ?(redefine=false) ?(cache=`No) f id =
    let str_id = Stateid.to_string id in
    if is_cached id && not redefine then
      anomaly (str"defining state "++str str_id++str" twice");
    try
      prerr_endline("defining "^str_id^" (cache="^
        if cache = `Yes then "Y" else if cache = `Shallow then "S" else "N");
      f ();
      if cache = `Yes then freeze `No id
      else if cache = `Shallow then freeze `Shallow id;
      prerr_endline ("setting cur id to "^str_id);
      cur_id := id;
      feedback ~state_id:id Interface.Processed;
      VCS.reached id true;
      if Proof_global.there_are_pending_proofs () then
        VCS.goals id (Proof_global.get_open_goals ());
    with e ->
      let e = Errors.push e in
      let good_id = !cur_id in
      cur_id := Stateid.dummy;
      VCS.reached id false;
      match Stateid.get e with
      | Some _ -> raise e
      | None -> raise (exn_on id ~valid:good_id e)

end
(* }}} *)


(* Slave processes (if initialized, otherwise local lazy evaluation) *)
module Slaves : sig

  (* (eventually) remote calls *)
  val build_proof :
    exn_info:(Stateid.t * Stateid.t) -> start:Stateid.t -> stop:Stateid.t ->
      future_proof

  (* blocking function that waits for the task queue to be empty *)
  val wait_all_done : unit -> unit
  
  (* initialize the whole machinery (optional) *)
  val init : unit -> unit

  (* slave process main loop *)
  val slave_main_loop : unit -> unit
  val slave_init_stdout : unit -> unit

  (* to disentangle modules *)
  val set_reach_known_state :
    (?redefine_qed:bool -> cache:Summary.marshallable -> Stateid.t -> unit) -> unit


end = struct (* {{{ *)

  module TQueue : sig

    type 'a t
    val create : unit -> 'a t
    val pop : 'a t -> 'a
    val push : 'a t -> 'a -> unit
    val wait_until_n_are_waiting_and_queue_empty : int -> 'a t -> unit

  end = struct (* {{{ *)

                 (* queue, lock, cond_q, n_waiting, cond_n_waiting *)
    type 'a t = 'a Queue.t * Mutex.t * Condition.t * int ref * Condition.t

    let create () =
      Queue.create (), Mutex.create (), Condition.create (),
      ref 0, Condition.create ()

    let pop (q,m,c,n,cn) =
      Mutex.lock m;
      while Queue.is_empty q do
        n := !n+1;
        Condition.signal cn;
        Condition.wait c m;
        n := !n-1
      done;
      let x = Queue.pop q in
      Condition.signal c;
      Condition.signal cn;
      Mutex.unlock m;
      x

    let push (q,m,c,n,cn) x =
      Mutex.lock m;
      Queue.push x q;
      Condition.signal c;
      Mutex.unlock m

    let wait_until_n_are_waiting_and_queue_empty (j : int) (q,m,c,n,cn) =
      Mutex.lock m;
      while not (Queue.is_empty q) || !n < j do Condition.wait cn m done;
      Mutex.unlock m

  end (* }}} *)

  module SlavesPool : sig
  
    val init : int -> ((unit -> in_channel * out_channel * int) -> unit) -> unit
    val is_empty : unit -> bool
    val n_slaves : unit -> int
  
  end = struct (* {{{ *)
  
    let slave_managers = ref None
    
    let n_slaves () = match !slave_managers with
      | None -> 0
      | Some managers -> Array.length managers
    let is_empty () = !slave_managers = None

    let respawn n () =
      let c2s_r, c2s_w = Unix.pipe () in
      let s2c_r, s2c_w = Unix.pipe () in
      Unix.set_close_on_exec c2s_w;
      Unix.set_close_on_exec s2c_r;
      let prog =  Sys.argv.(0) in
      let rec set_slave_opt = function
        | [] -> ["-coq-slaves"; string_of_int n]
        | ("-ideslave"|"-emacs"|"-emacs-U")::tl -> set_slave_opt tl
        | ("-coq-slaves"
          |"-compile"
          |"-compile-verbose")::_::tl -> set_slave_opt tl
        | x::tl -> x :: set_slave_opt tl in
      let args = Array.of_list (set_slave_opt (Array.to_list Sys.argv)) in
      prerr_endline ("EXEC: " ^ prog ^ " " ^
        (String.concat " " (Array.to_list args)));
      let env = Array.append !coq_slave_extra_env (Unix.environment ()) in
      let pid = Unix.create_process_env prog args env c2s_r s2c_w Unix.stderr in
      Unix.close c2s_r;
      Unix.close s2c_w;
      let s =
        Unix.in_channel_of_descr s2c_r, Unix.out_channel_of_descr c2s_w, pid in
      s

    let init n manage_slave =
      slave_managers := Some
        (Array.init n (fun x -> Thread.create manage_slave (respawn (x+1))));

  end (* }}} *)
  
  let reach_known_state = ref (fun ?redefine_qed ~cache id -> ())
  let set_reach_known_state f = reach_known_state := f

  type request = ReqBuildProof of (Stateid.t * Stateid.t) * Stateid.t * VCS.vcs

  type response =
    | RespBuiltProof of Proof_global.closed_proof_output
    | RespError of Stateid.t * Stateid.t * std_ppcmds (* err, safe, msg *)
    | RespFeedback of Interface.feedback
    | RespGetCounterFreshLocalUniv
    | RespGetCounterNewUnivLevel
  let pr_response = function
    | RespBuiltProof _ -> "Sucess"
    | RespError _ -> "Error"
    | RespFeedback { Interface.id = Interface.State id } ->
        "Feedback on " ^ Stateid.to_string id
    | RespFeedback _ -> assert false
    | RespGetCounterFreshLocalUniv -> "GetCounterFreshLocalUniv"
    | RespGetCounterNewUnivLevel -> "GetCounterNewUnivLevel"

  type more_data =
    | MoreDataLocalUniv of Univ.universe list
    | MoreDataUnivLevel of Univ.universe_level list
 
  type task =
    | TaskBuildProof of (Stateid.t * Stateid.t) * Stateid.t * Stateid.t *
        (Proof_global.closed_proof_output Future.assignement -> unit)
  let pr_task = function
    | TaskBuildProof(_,bop,eop,_) ->
        "TaskBuilProof("^Stateid.to_string bop^","^Stateid.to_string eop^")"

  let request_of_task task =
    match task with
    | TaskBuildProof (exn_info,bop,eop,_) ->
        ReqBuildProof(exn_info,eop,
          VCS.slice ~start:eop ~stop:bop ~purify:State.make_shallow)

  let build_proof_here (id,valid) eop =
    Future.create (fun () ->
      !reach_known_state ~cache:`No eop;
      let p = Proof_global.return_proof ~fix_exn:(State.exn_on id ~valid) in
      p)

  let slave_respond msg =
    match msg with
    | ReqBuildProof(exn_info,eop, vcs) ->
        VCS.restore vcs;
        VCS.print ();
        let r = RespBuiltProof (
          let l = Future.force (build_proof_here exn_info eop) in
          List.iter (fun (_,se) -> Declareops.iter_side_effects (function
            | Declarations.SEsubproof(_,
               { Declarations.const_body = Declarations.OpaqueDef f;
                 const_universes = cst} ) -> 
                  ignore(Future.force f); ignore(Future.force cst)
            | _ -> ())
          se) (fst l);
          l) in
        VCS.print ();
        r

  open Interface

  exception MarshalError of string

  let marshal_to_channel oc data =
    Marshal.to_channel oc data [];
    flush oc

  let marshal_request oc (req : request) =
    try marshal_to_channel oc req
    with Invalid_argument s -> raise (MarshalError ("marshal_request: "^s))

  let unmarshal_request ic =
    try (Marshal.from_channel ic : request)
    with Invalid_argument s -> raise (MarshalError ("unmarshal_request: "^s))

  let marshal_response oc (res : response) =
    try marshal_to_channel oc res
    with Invalid_argument s -> raise (MarshalError ("marshal_response: "^s))
  
  let unmarshal_response ic =
    try (Marshal.from_channel ic : response)
    with Invalid_argument s -> raise (MarshalError ("unmarshal_response: "^s))
  
  let marshal_more_data oc (res : more_data) =
    try marshal_to_channel oc res
    with Invalid_argument s -> raise (MarshalError ("marshal_more_data: "^s))
  
  let unmarshal_more_data ic =
    try (Marshal.from_channel ic : more_data)
    with Invalid_argument s -> raise (MarshalError ("unmarshal_more_data: "^s))

  let queue : task TQueue.t = TQueue.create ()

  let wait_all_done () =
    TQueue.wait_until_n_are_waiting_and_queue_empty
      (SlavesPool.n_slaves ()) queue

  let build_proof ~exn_info ~start ~stop =
    if SlavesPool.is_empty () then
      build_proof_here exn_info stop
    else 
      let f, assign = Future.create_delegate () in
      Pp.feedback (Interface.InProgress 1);
      TQueue.push queue (TaskBuildProof(exn_info,start,stop,assign));
      f

  exception RemoteException of std_ppcmds
  let _ = Errors.register_handler (function
    | RemoteException ppcmd -> ppcmd
    | _ -> raise Unhandled)

  let rec manage_slave respawn =
    let ic, oc, pid = respawn () in
    let kill_pid =
      ref (fun () -> try Unix.kill pid 9 with Unix.Unix_error _ -> ()) in
    at_exit (fun () -> !kill_pid ());
    let last_task = ref None in
    try
      while true do
        let task = TQueue.pop queue in
        last_task := Some task;
        try
          marshal_request oc (request_of_task task);
          let rec loop () =
            let response = unmarshal_response ic in
            match task, response with
            | TaskBuildProof(_,_,_, assign), RespBuiltProof pl ->
                assign (`Val pl);
                Pp.feedback (Interface.InProgress ~-1)
            | TaskBuildProof(_,_,_, assign), RespError (err_id,valid,e) ->
                let e = Stateid.add ~valid (RemoteException e) err_id in
                assign (`Exn e);
                Pp.feedback (Interface.InProgress ~-1)
            | _, RespGetCounterFreshLocalUniv -> assert false (* Deprecated function *)
                (* marshal_more_data oc (MoreDataLocalUniv *)
                (*   (CList.init 10 (fun _ -> Universes.fresh_local_univ ()))); *)
                (* loop () *)
            | _, RespGetCounterNewUnivLevel ->
                marshal_more_data oc (MoreDataUnivLevel
                  (CList.init 10 (fun _ -> Universes.new_univ_level (Global.current_dirpath ()))));
                loop ()
            | _, RespFeedback {id = State state_id; content = msg} ->
                Pp.feedback ~state_id msg;
                loop ()
            | _, RespFeedback _ -> assert false (* Parsing in master process *)
          in
            loop (); last_task := None
        with
        | VCS.Expired -> (* task cancelled: e.g. the user did backtrack *)
            Pp.feedback (Interface.InProgress ~-1);
            prerr_endline ("Task expired: " ^ pr_task task)
        | MarshalError s when !fallback_to_lazy_if_marshal_error ->
            msg_warning(strbrk("Marshalling error: "^s^". "^
              "The system state could not be sent to the slave process. "^
              "Falling back to local, lazy, evaluation."));
            let TaskBuildProof (exn_info, _, stop, assign) = task in
            assign(`Comp(build_proof_here exn_info stop));
            Pp.feedback (Interface.InProgress ~-1)
        | (Sys_error _ | Invalid_argument _ | End_of_file) as e -> raise e
        | MarshalError s ->
            Printf.eprintf "Fatal marshal error: %s\n" s;
            flush_all (); exit 1
        | e ->
            prerr_endline ("Uncaught exception in slave manager: "^
              string_of_ppcmds (print e))
            (* XXX do something sensible *)
      done
    with
    | Sys_error _ | Invalid_argument _ | End_of_file
      when !fallback_to_lazy_if_slave_dies ->
        kill_pid := (fun () -> ());
        msg_warning(strbrk "The slave process died badly.");
        (match !last_task with
        | Some task ->
            msg_warning(strbrk "Falling back to local, lazy, evaluation.");
            let TaskBuildProof (exn_info, _, stop, assign) = task in
            assign(`Comp(build_proof_here exn_info stop));
            Pp.feedback (Interface.InProgress ~-1);
        | None -> ());
        ignore(Unix.waitpid [] pid);
        close_in ic;
        close_out oc;
        manage_slave respawn
    | Sys_error _ | Invalid_argument _ | End_of_file ->
        let exit_status pid = match Unix.waitpid [] pid with
          | _, Unix.WEXITED i -> Printf.sprintf "exit(%d)" i
          | _, Unix.WSIGNALED sno -> Printf.sprintf "signalled(%d)" sno
          | _, Unix.WSTOPPED sno -> Printf.sprintf "stopped(%d)" sno in
        Printf.eprintf "Fatal slave error: %s\n" (exit_status pid);
        flush_all (); exit 1
                    

  let init () = SlavesPool.init !Flags.coq_slaves_number manage_slave

  let slave_ic = ref stdin
  let slave_oc = ref stdout

  let slave_init_stdout () =
    slave_oc := Unix.out_channel_of_descr (Unix.dup Unix.stdout);
    slave_ic := Unix.in_channel_of_descr (Unix.dup Unix.stdin);
    set_binary_mode_out !slave_oc true;
    set_binary_mode_in !slave_ic true;
    Unix.dup2 Unix.stderr Unix.stdout

  let bufferize f =
    let l = ref [] in
    fun () ->
      match !l with
      | [] -> let data = f () in l := List.tl data; List.hd data
      | x::tl -> l := tl; x

  let slave_main_loop () =
    let slave_feeder oc fb =
      Marshal.to_channel oc (RespFeedback fb) [];
      flush oc in
    Pp.set_feeder (slave_feeder !slave_oc);
    Universes.set_remote_new_univ_level (bufferize (fun () ->
      marshal_response !slave_oc RespGetCounterNewUnivLevel;
      match unmarshal_more_data !slave_ic with
      | MoreDataUnivLevel l -> l | _ -> assert false));
    (* Univ.set_remote_fresh_local_univ (bufferize (fun () -> *)
    (*   marshal_response !slave_oc RespGetCounterFreshLocalUniv; *)
    (*   match unmarshal_more_data !slave_ic with *)
    (*   | MoreDataLocalUniv l -> l | _ -> assert false)); *)
    while true do
      try
        let request = unmarshal_request !slave_ic in
        let response = slave_respond request in
        marshal_response !slave_oc response;
      with
      | MarshalError s ->
        Printf.eprintf "Slave: fatal marshal error: %s\n" s;
        flush_all (); exit 2
      | e when Errors.noncritical e ->
        (* This can happen if the proof is broken.  The error has also been
         * signalled as a feedback, hence we can silently recover *)
        let err_id, safe_id = match Stateid.get e with
          | Some (safe, err) -> err, safe
          | None -> Stateid.dummy, Stateid.dummy in
        marshal_response !slave_oc (RespError (err_id, safe_id, print e));
        prerr_endline "Slave: failed with the following exception:";
        prerr_endline (string_of_ppcmds (print e))
      | e ->
        Printf.eprintf "Slave: failed with the following CRITICAL exception: %s\n"
          (Pp.string_of_ppcmds (print e));  
        flush_all (); exit 1
    done

end (* }}} *)

(* Runs all transactions needed to reach a state *)
module Reach : sig

  val known_state :
    ?redefine_qed:bool -> cache:Summary.marshallable -> Stateid.t -> unit

end = struct (* {{{ *)

let pstate = ["meta counter"; "evar counter"; "program-tcc-table"]

let delegate_policy_check l =
  (interactive () = `Yes || List.length l > 20) &&
  (if interactive () = `Yes then !Flags.coq_slave_mode = 0 else true)

let collect_proof cur hd id =
 prerr_endline ("Collecting proof ending at "^Stateid.to_string id); 
 let is_defined = function
   | _, (_, _, VernacEndProof (Proved (false,_))) -> true
   | _ -> false in
 let rec collect last accn id =
    let view = VCS.visit id in
    match last, view.step with
    | _, `Cmd (x, _) -> collect (Some (id,x)) (id::accn) view.next
    | _, `Alias _ -> collect None (id::accn) view.next
    | _, `Fork(_,_,_::_::_,_)->
        `NotOptimizable `MutualProofs (* TODO: understand where we need that *)
    | _, `Fork(_,_,_,true)->
        `NotOptimizable `Polymorphic
    | Some (parent, (_,_,VernacProof(_,Some _) as v)), `Fork (_, hd', _, false) ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        if delegate_policy_check accn then `Optimizable (parent, Some v, accn)
        else `NotOptimizable `TooShort
    | Some (parent, _), `Fork (_, hd', _, false) ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        if delegate_policy_check accn then `MaybeOptimizable (parent, accn)
        else `NotOptimizable `TooShort
    | _, `Sideff se -> collect None (id::accn) view.next
    | _ -> `NotOptimizable `Unknown in
 match cur, (VCS.visit id).step with
 | (parent, (_,_,VernacExactProof _)), `Fork _ ->
     `NotOptimizable `Immediate
 | _ ->
     if State.is_cached id then `NotOptimizable `AlreadyEvaluated
     else if is_defined cur then `NotOptimizable `Transparent
     else collect (Some cur) [] id

let known_state ?(redefine_qed=false) ~cache id =

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let cherry_pick_non_pstate () =
    Summary.freeze_summary ~marshallable:`No ~complement:true pstate,
    Lib.freeze ~marshallable:`No in
  let inject_non_pstate (s,l) = Summary.unfreeze_summary s; Lib.unfreeze l in

  let rec pure_cherry_pick_non_pstate id = Future.purify (fun id ->
    prerr_endline ("cherry-pick non pstate " ^ Stateid.to_string id);
    reach id;
    cherry_pick_non_pstate ()) id

  (* traverses the dag backward from nodes being already calculated *)
  and reach ?(redefine_qed=false) ?(cache=cache) id =
    prerr_endline ("reaching: " ^ Stateid.to_string id);
    if not redefine_qed && State.is_cached id then begin
      State.install_cached id;
      feedback ~state_id:id Interface.Processed;
      prerr_endline ("reached (cache)")
    end else
    let step, cache_step =
      let view = VCS.visit id in
      match view.step with
      | `Alias id -> (fun () ->
            reach view.next; reach id; Vernacentries.try_print_subgoals ()
          ), cache
      | `Cmd (x,_) -> (fun () ->
            reach view.next; vernac_interp id x
          ), cache
      | `Fork (x,_,_,_) -> (fun () ->
            reach view.next; vernac_interp id x
          ), `Yes
      | `Qed ({ qast = x; keep; brinfo; brname } as qed, eop) ->
          let rec aux = function
          | `Optimizable (start, proof_using_ast, nodes) -> (fun () ->
                prerr_endline ("Optimizable " ^ Stateid.to_string id);
                VCS.create_cluster nodes ~tip:id;
                begin match keep, brinfo, qed.fproof with
                | VtKeep, { VCS.kind = `Edit _ }, None -> assert false
                | VtKeep, { VCS.kind = `Edit _ }, Some ofp ->
                    assert(redefine_qed = true);
                    VCS.create_cluster nodes ~tip:id;
                    let fp =
                      Slaves.build_proof ~exn_info:(id,eop) ~start ~stop:eop in
                    Future.replace ofp fp;
                    qed.fproof <- Some fp
                | VtKeep, { VCS.kind = `Proof _ }, Some _ -> assert false
                | VtKeep, { VCS.kind = `Proof _ }, None ->
                    reach ~cache:`Shallow start;
                    let fp =
                      Slaves.build_proof ~exn_info:(id,eop) ~start ~stop:eop in
                    qed.fproof <- Some fp;
                    let proof = Proof_global.close_future_proof fp in
                    reach view.next;
                    vernac_interp id ~proof x
                | VtDrop, _, _ ->
                    reach view.next;
                    Option.iter (vernac_interp start) proof_using_ast;
                    vernac_interp id x
                | _, { VCS.kind = `Master }, _ -> assert false
                end;
                Proof_global.discard_all ()
              ), if redefine_qed then `No else `Yes
          | `NotOptimizable `Immediate -> (fun () -> 
                assert (Stateid.equal view.next eop);
                reach eop; vernac_interp id x; Proof_global.discard_all ()
              ), `Yes
          | `NotOptimizable _ -> (fun () ->
                prerr_endline ("NotOptimizable " ^ Stateid.to_string id);
                reach eop;
                begin match keep with
                | VtKeep ->
                    let proof = Proof_global.close_proof () in
                    reach view.next;
                    vernac_interp id ~proof x
                | VtDrop ->
                    reach view.next;
                    vernac_interp id x
                end;
                Proof_global.discard_all ()
              ), `Yes
          | `MaybeOptimizable (start, nodes) -> (fun () ->
                prerr_endline ("MaybeOptimizable " ^ Stateid.to_string id);
                reach ~cache:`Shallow start;
                (* no sections and no modules *)
                if List.is_empty (Environ.named_context (Global.env ())) &&
                   Safe_typing.is_curmod_library (Global.safe_env ()) then
                  fst (aux (`Optimizable (start, None, nodes))) ()
                else
                  fst (aux (`NotOptimizable `Unknown)) ()
              ), if redefine_qed then `No else `Yes
          in
          aux (collect_proof (view.next, x) brname eop)
      | `Sideff (`Ast (x,_)) -> (fun () ->
            reach view.next; vernac_interp id x
          ), cache
      | `Sideff (`Id origin) -> (fun () ->
            let s = pure_cherry_pick_non_pstate origin in
            reach view.next;
            inject_non_pstate s
          ), cache
    in
    State.define ~cache:cache_step ~redefine:redefine_qed step id;
    prerr_endline ("reached: "^ Stateid.to_string id) in
  reach ~redefine_qed id

end (* }}} *)
let _ = Slaves.set_reach_known_state Reach.known_state

(* The backtrack module simulates the classic behavior of a linear document *)
module Backtrack : sig

  val record : unit -> unit
  val backto : Stateid.t -> unit

  (* we could navigate the dag, but this ways easy *)
  val branches_of : Stateid.t -> backup

  (* To be installed during initialization *)
  val undo_vernac_classifier : vernac_expr -> vernac_classification

end = struct (* {{{ *)

  let record () =
    let current_branch = VCS.current_branch () in
    let mine = current_branch, VCS.get_branch current_branch in
    let info = VCS.get_info (VCS.get_branch_pos current_branch) in
    let others =
      CList.map_filter (fun b ->
        if Vcs_.Branch.equal b current_branch then None
        else Some(b, VCS.get_branch b)) (VCS.branches ()) in
    info.vcs_backup <- Some (VCS.backup ()), Some { mine; others }

  let backto oid =
    let info = VCS.get_info oid in
    match info.vcs_backup with
    | None, _ -> anomaly(str"Backtrack.backto to a state with no vcs_backup")
    | Some vcs, _ ->
        VCS.restore vcs;
        let id = VCS.get_branch_pos (VCS.current_branch ()) in
        if not (Stateid.equal id oid) then
          anomaly (str "Backtrack.backto did not jump to the right state")

  let branches_of id =
    let info = VCS.get_info id in
    match info.vcs_backup with
    | _, None ->
       anomaly(str"Backtrack.branches_of on a state with no vcs_backup")
    | _, Some x -> x

  let rec fold_until f acc id =
    let next acc =
      if id = Stateid.initial then raise Not_found
      else fold_until f acc (VCS.visit id).next in
    let info = VCS.get_info id in
    match info.vcs_backup with
    | None, _ -> next acc
    | Some vcs, _ ->
        let ids =
          if id = Stateid.initial || id = Stateid.dummy then [] else
          match VCS.visit id with
          | { step = `Fork (_,_,l,_) } -> l
          | { step = `Cmd (_,l) } -> l
          | _ -> [] in
        match f acc (id, vcs, ids) with
        | Stop x -> x
        | Next acc -> next acc
 
  let undo_vernac_classifier v =
    try
      match v with
      | VernacResetInitial ->
          VtStm (VtBack Stateid.initial, true), VtNow
      | VernacResetName (_,name) ->
          msg_warning
            (str"Reset not implemented for automatically generated constants");
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          (try
            let oid =
              fold_until (fun b (id,_,label) ->
                if b then Stop id else Next (List.mem name label))
              false id in
            VtStm (VtBack oid, true), VtNow
          with Not_found ->
            VtStm (VtBack id, true), VtNow)
      | VernacBack n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then Stop id else Next (n-1)) n id in
          VtStm (VtBack oid, true), VtNow
      | VernacUndo n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then Stop id else Next (n-1)) n id in
          VtStm (VtBack oid, true), VtLater
      | VernacUndoTo _
      | VernacRestart as e ->
          let m = match e with VernacUndoTo m -> m | _ -> 0 in
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let vcs =
            match (VCS.get_info id).vcs_backup with 
            | None, _ -> anomaly(str"Backtrack: tip with no vcs_backup")
            | Some vcs, _ -> vcs in
          let cb, _ =
            Vcs_aux.find_proof_at_depth vcs (Vcs_aux.proof_nesting vcs) in
          let n = fold_until (fun n (_,vcs,_) ->
            if List.mem cb (Vcs_.branches vcs) then Next (n+1) else Stop n)
            0 id in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then Stop id else Next (n-1)) (n-m-1) id in
          VtStm (VtBack oid, true), VtLater
      | VernacAbortAll ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun () (id,vcs,_) ->
            match Vcs_.branches vcs with [_] -> Stop id | _ -> Next ())
            () id in
          VtStm (VtBack oid, true), VtLater
      | VernacBacktrack (id,_,_)
      | VernacBackTo id ->
          VtStm (VtBack (Stateid.of_int id), true), VtNow
      | _ -> VtUnknown, VtNow
    with
    | Not_found ->
       msg_warning(str"undo_vernac_classifier: going back to the initial state.");
       VtStm (VtBack Stateid.initial, true), VtNow

end (* }}} *)

let init () =
  VCS.init Stateid.initial;
  set_undo_classifier Backtrack.undo_vernac_classifier;
  State.define ~cache:`Yes (fun () -> ()) Stateid.initial;
  Backtrack.record ();
  if Int.equal !Flags.coq_slave_mode 0 then begin (* We are the master process *)
    Slaves.init ();
    let opts = match !Flags.coq_slave_options with
      | None -> []
      | Some s -> Str.split_delim (Str.regexp ",") s in
    if List.mem "fallback-to-lazy-if-marshal-error=no" opts then
      fallback_to_lazy_if_marshal_error := false;
    if List.mem "fallback-to-lazy-if-slave-dies=no" opts then
      fallback_to_lazy_if_slave_dies := false;
    try
      let env_opt = Str.regexp "^extra-env=" in
      let env = List.find (fun s -> Str.string_match env_opt s 0) opts in
      coq_slave_extra_env := Array.of_list
        (Str.split_delim (Str.regexp ";") (Str.replace_first env_opt "" env))
    with Not_found -> ()
  end

let slave_main_loop () = Slaves.slave_main_loop ()

let slave_init_stdout () = Slaves.slave_init_stdout ()

let observe id =
  let vcs = VCS.backup () in
  try
    Reach.known_state ~cache:(interactive ()) id;
    VCS.print ()
  with e ->
    let e = Errors.push e in
    VCS.print ();
    VCS.restore vcs;
    raise e

let finish () =
  observe (VCS.get_branch_pos (VCS.current_branch ()));
  VCS.print ()

let join () =
  let rec jab id =
    if Stateid.equal id Stateid.initial then ()
    else
      let view = VCS.visit id in
      match view.step with
      | `Qed ({ keep = VtDrop }, eop) ->
           Future.purify observe eop; jab view.next
      | _ -> jab view.next in
  finish ();
  VCS.print ();
  Slaves.wait_all_done ();
  prerr_endline "Joining the environment";
  Global.join_safe_environment ();
  VCS.print ();
  prerr_endline "Joining the aborted proofs";
  jab (VCS.get_branch_pos VCS.Branch.master);
  VCS.print ()

let merge_proof_branch qast keep brname =
  let brinfo = VCS.get_branch brname in
  let qed fproof = { qast; keep; brname; brinfo; fproof } in
  match brinfo with
  | { VCS.kind = `Proof _ } ->
      VCS.checkout VCS.Branch.master;
      let id = VCS.new_node () in
      VCS.merge id ~ours:(Qed (qed None)) brname;
      VCS.delete_branch brname;
      if keep == VtKeep then VCS.propagate_sideff None;
      `Ok
  | { VCS.kind = `Edit (mode, qed_id, master_id) } ->
      let ofp =
        match VCS.visit qed_id with
        | { step = `Qed ({ fproof }, _) } -> fproof
        | _ -> assert false in
      VCS.rewrite_merge qed_id ~ours:(Qed (qed ofp)) ~at:master_id brname;
      VCS.delete_branch brname;
      VCS.gc ();
      Reach.known_state ~redefine_qed:true ~cache:`No qed_id;
      VCS.checkout VCS.Branch.master;
      `Unfocus qed_id
  | { VCS.kind = `Master } ->
       raise (State.exn_on Stateid.dummy Proof_global.NoCurrentProof)

let process_transaction ~tty verbose c (loc, expr) =
  let warn_if_pos a b =
    if b then msg_warning(pr_ast a ++ str" should not be part of a script") in
  let v, x = expr, (verbose && Flags.is_verbose(), loc, expr) in
  prerr_endline ("{{{ execute: "^ string_of_ppcmds (pr_ast x));
  let vcs = VCS.backup () in
  try
    let head = VCS.current_branch () in
    VCS.checkout head;
    let rc = begin
      prerr_endline ("  classified as: " ^ string_of_vernac_classification c);
      match c with
      (* Joining various parts of the document *)
      | VtStm (VtJoinDocument, b), VtNow -> warn_if_pos x b; join (); `Ok
      | VtStm (VtFinish, b),       VtNow -> warn_if_pos x b; finish (); `Ok
      | VtStm (VtPrintDag, b), VtNow ->
          warn_if_pos x b; VCS.print ~now:true (); `Ok
      | VtStm (VtObserve id, b),   VtNow -> warn_if_pos x b; observe id; `Ok
      | VtStm ((VtObserve _ | VtFinish | VtJoinDocument|VtPrintDag),_), VtLater ->
          anomaly(str"classifier: join actions cannot be classified as VtLater")
      
      (* Back *)
      | VtStm (VtBack oid, true), w ->
          let id = VCS.new_node () in
          let { mine; others } = Backtrack.branches_of oid in
          List.iter (fun branch ->
            if not (List.mem_assoc branch (mine::others)) then
              ignore(merge_proof_branch x VtDrop branch))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          VCS.commit id (Alias oid);
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtStm (VtBack id, false), VtNow ->
          prerr_endline ("undo to state " ^ Stateid.to_string id);
          Backtrack.backto id;
          VCS.checkout_shallowest_proof_branch ();
          Reach.known_state ~cache:(interactive ()) id; `Ok
      | VtStm (VtBack id, false), VtLater ->
          anomaly(str"classifier: VtBack + VtLater must imply part_of_script")

      (* Query *)
      | VtQuery false, VtNow when tty = true ->
          finish ();
          (try Future.purify (vernac_interp Stateid.dummy) (true,loc,expr)
           with e when Errors.noncritical e ->
             let e = Errors.push e in
             raise(State.exn_on Stateid.dummy e)); `Ok
      | VtQuery false, VtNow ->
          (try vernac_interp Stateid.dummy x
           with e when Errors.noncritical e ->
             let e = Errors.push e in
             raise(State.exn_on Stateid.dummy e)); `Ok
      | VtQuery true, w ->
          let id = VCS.new_node () in
          VCS.commit id (Cmd (x,[]));
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtQuery false, VtLater ->
          anomaly(str"classifier: VtQuery + VtLater must imply part_of_script")

      (* Proof *)
      | VtStartProof (mode, names, poly), w ->
          let id = VCS.new_node () in
          let bname = VCS.mk_branch_name x in
          VCS.checkout VCS.Branch.master;
          VCS.commit id (Fork (x, bname, names, poly));
          VCS.branch bname (`Proof (mode, VCS.proof_nesting () + 1));
          Proof_global.activate_proof_mode mode;
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtProofMode _, VtLater ->
          anomaly(str"VtProofMode must be executed VtNow")
      | VtProofMode mode, VtNow ->
          let id = VCS.new_node () in
          VCS.checkout VCS.Branch.master;
          VCS.commit id (Cmd (x,[]));
          VCS.propagate_sideff (Some x);
          List.iter
            (fun bn -> match VCS.get_branch bn with
            | { VCS.root; kind = `Master; pos } -> ()
            | { VCS.root; kind = `Proof(_,d); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Proof(mode,d))
            | { VCS.root; kind = `Edit(_,f,q); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Edit(mode,f,q)))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record ();
          finish ();
          `Ok
      | VtProofStep, w ->
          let id = VCS.new_node () in
          VCS.commit id (Cmd (x,[]));
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtQed keep, w ->
          let rc = merge_proof_branch x keep head in
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish ();
          rc
          
      (* Side effect on all branches *)
      | VtSideff l, w ->
          let id = VCS.new_node () in
          VCS.checkout VCS.Branch.master;
          VCS.commit id (Cmd (x,l));
          VCS.propagate_sideff (Some x);
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish (); `Ok

      (* Unknown: we execute it, check for open goals and propagate sideeff *)
      | VtUnknown, VtNow ->
          let id = VCS.new_node () in
          let step () =
            VCS.checkout VCS.Branch.master;
            let mid = VCS.get_branch_pos VCS.Branch.master in
            Reach.known_state ~cache:(interactive ()) mid;
            vernac_interp id x;
            (* Vernac x may or may not start a proof *)
            if VCS.Branch.equal head VCS.Branch.master &&
               Proof_global.there_are_pending_proofs ()
            then begin
              let bname = VCS.mk_branch_name x in
              VCS.commit id (Fork (x,bname,[],false));
              VCS.branch bname (`Proof ("Classic", VCS.proof_nesting () + 1));
              Proof_global.activate_proof_mode "Classic";
            end else begin
              VCS.commit id (Cmd (x,[]));
              VCS.propagate_sideff (Some x);
              VCS.checkout_shallowest_proof_branch ();
            end in
          State.define ~cache:`Yes step id;
          Backtrack.record (); `Ok

      | VtUnknown, VtLater ->
          anomaly(str"classifier: VtUnknown must imply VtNow")
    end in
    (* Proof General *)
    begin match v with 
      | VernacStm (PGLast _) ->
        if not (VCS.Branch.equal head VCS.Branch.master) then
          vernac_interp Stateid.dummy
            (true,Loc.ghost,VernacShow (ShowGoal OpenSubgoals))
      | _ -> ()
    end;
    prerr_endline "executed }}}";
    VCS.print ();
    rc
  with e ->
    let e = Errors.push e in
    match Stateid.get e with
    | None ->
        VCS.restore vcs;
        VCS.print ();
        anomaly (str ("execute: "^ 
          string_of_ppcmds (Errors.print_no_report e) ^ "}}}"))
    | Some (safe_id, id) ->
        prerr_endline ("Failed at state " ^ Stateid.to_string id);
        VCS.restore vcs;
        if tty then begin (* We stay on a valid state *)
          prerr_endline ("Safe state " ^ Stateid.to_string safe_id);
	  Backtrack.backto safe_id;
          VCS.checkout_shallowest_proof_branch ();
          Reach.known_state ~cache:(interactive ()) safe_id;
        end else begin
          VCS.print ()
        end;
        raise e

(** STM interface {{{******************************************************* **)

let query ~at s =
  Future.purify (fun s ->
    if Stateid.equal at Stateid.dummy then finish ()
    else Reach.known_state ~cache:`Yes at;
    let loc_ast = vernac_parse 0 s in
    ignore(process_transaction ~tty:false true (VtQuery false, VtNow) loc_ast))
  s

let add ~ontop ?(check=ignore) verb eid s =
  let cur_tip = VCS.cur_tip () in
  if Stateid.equal ontop cur_tip then begin
    let _, ast as loc_ast = vernac_parse eid s in
    check(loc_ast);
    let clas = classify_vernac ast in
    match process_transaction ~tty:false verb clas loc_ast with
    | `Ok -> VCS.cur_tip (), `NewTip
    | `Unfocus qed_id -> qed_id, `Unfocus (VCS.cur_tip ())
  end else begin
    (* For now, arbitrary edits should be announced with edit_at *)
    anomaly(str"Not yet implemented, the GUI should not try this")
  end

type focus = {
  start : Stateid.t;
  stop : Stateid.t;
  tip : Stateid.t
}

let edit_at id =
  let vcs = VCS.backup () in
  let on_cur_branch id =
    let rec aux cur =
      if id = cur then true
      else match VCS.visit cur with
      | { step = `Fork _ } -> false
      | { next } -> aux next in
    aux (VCS.get_branch_pos (VCS.current_branch ())) in
  let is_ancestor_of_cur_branch id =
    Vcs_.NodeSet.mem id
      (VCS.reachable (VCS.get_branch_pos (VCS.current_branch ()))) in
  let has_failed qed_id =
    match VCS.visit qed_id with
    | { step = `Qed ({ fproof = Some fp }, _) } -> Future.is_exn fp
    | _ -> false in
  let rec master_for_br root tip =
      if Stateid.equal tip Stateid.initial then tip else
      match VCS.visit tip with
      | { next } when next = root -> root
      | { step = `Fork _ } -> tip
      | { step = `Sideff (`Ast(_,id)|`Id id) } -> id
      | { next } -> master_for_br root next in
  let reopen_branch at_id mode qed_id tip =
    VCS.delete_cluster_of id;
    let master_id =
      match VCS.visit qed_id with
      | { step = `Qed _; next = master_id } -> master_id
      | _ -> anomaly (str "Cluster not ending with Qed") in
    VCS.branch ~root:master_id ~pos:id
      VCS.edit_branch (`Edit (mode, qed_id, master_id));
    Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `Focus { stop = qed_id; start = master_id; tip } in
  let backto id =
    List.iter VCS.delete_branch (VCS.branches ());
    let ancestors = VCS.reachable id in
    let { mine = brname, brinfo; others } = Backtrack.branches_of id in
    List.iter (fun (name,{ VCS.kind = k; root; pos }) ->
      if not(VCS.Branch.equal name VCS.Branch.master) &&
         Vcs_.NodeSet.mem root ancestors then
        VCS.branch ~root ~pos name k)
      others;
    VCS.reset_branch VCS.Branch.master (master_for_br brinfo.VCS.root id);
    VCS.branch ~root:brinfo.VCS.root ~pos:brinfo.VCS.pos brname brinfo.VCS.kind;
    VCS.delete_cluster_of id;
    VCS.gc ();
    Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `NewTip in
  try
    let rc =
      let focused = List.exists ((=) VCS.edit_branch) (VCS.branches ()) in
      let branch_info =
        match snd (VCS.get_info id).vcs_backup with
        | Some{ mine = _, { VCS.kind = (`Proof(m,_)|`Edit(m,_,_)) }} -> Some m
        | _ -> None in
      match focused, VCS.cluster_of id, branch_info with
      | _, Some _, None -> assert false
      | false, Some qed_id, Some mode ->
          let tip = VCS.cur_tip () in
          if has_failed qed_id then reopen_branch id mode qed_id tip
          else backto id
      | true, Some qed_id, Some mode ->
          if on_cur_branch id then begin
            assert false
          end else if is_ancestor_of_cur_branch id then begin
            backto id
          end else begin
            anomaly(str"Cannot leave an `Edit branch open")
          end
      | true, None, _ ->
          if on_cur_branch id then begin
            VCS.reset_branch (VCS.current_branch ()) id;
            Reach.known_state ~cache:(interactive ()) id;
            VCS.checkout_shallowest_proof_branch ();
            `NewTip
          end else if is_ancestor_of_cur_branch id then begin
            backto id
          end else begin
            anomaly(str"Cannot leave an `Edit branch open")
          end
      | false, None, _ -> backto id
    in
    VCS.print ();
    rc
  with e ->
    let e = Errors.push e in
    match Stateid.get e with
    | None ->
        VCS.print ();
        anomaly (str ("edit_at: "^string_of_ppcmds (Errors.print_no_report e)))
    | Some (_, id) ->
        prerr_endline ("Failed at state " ^ Stateid.to_string id);
        VCS.restore vcs;
        VCS.print ();
        raise e
(* }}} *)

(** Old tty interface {{{*************************************************** **)

let interp verb (_,e as lexpr) =
  let clas = classify_vernac e in
  let rc = process_transaction ~tty:true verb clas lexpr in
  if rc <> `Ok then anomaly(str"tty loop can't be mixed with the STM protocol");
  if interactive () = `Yes then finish ()

let get_current_state () = VCS.cur_tip ()

let current_proof_depth () =
  let head = VCS.current_branch () in
  match VCS.get_branch head with
  | { VCS.kind = `Master } -> 0
  | { VCS.pos = cur; VCS.kind = (`Proof _ | `Edit _); VCS.root = root } ->
      let rec distance root =
        if Stateid.equal cur root then 0
        else 1 + distance (VCS.visit cur).next in
      distance cur

let unmangle n =
  let n = VCS.Branch.to_string n in
  let idx = String.index n '_' + 1 in
  Names.id_of_string (String.sub n idx (String.length n - idx))

let proofname b = match VCS.get_branch b with
  | { VCS.kind = (`Proof _| `Edit _) } -> Some b
  | _ -> None

let get_all_proof_names () =
  List.map unmangle (List.map_filter proofname (VCS.branches ()))

let get_current_proof_name () =
  Option.map unmangle (proofname (VCS.current_branch ()))

let get_script prf =
  let rec find acc id =
    if Stateid.equal id Stateid.initial || Stateid.equal id Stateid.dummy then acc else
    let view = VCS.visit id in
    match view.step with
    | `Fork (_,_,ns,_) when List.mem prf ns -> acc
    | `Qed (qed, proof) -> find [pi3 qed.qast, (VCS.get_info id).n_goals] proof
    | `Sideff (`Ast (x,_)) ->
         find ((pi3 x, (VCS.get_info id).n_goals)::acc) view.next
    | `Sideff (`Id id)  -> find acc id
    | `Cmd (x,_) -> find ((pi3 x, (VCS.get_info id).n_goals)::acc) view.next 
    | `Alias id -> find acc id
    | `Fork _ -> find acc view.next
    in
  find [] (VCS.get_branch_pos VCS.Branch.master)

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

let show_script ?proof () =
  try
    let prf =
      match proof with
      | None -> Pfedit.get_current_proof_name ()
      | Some (id,_) -> id in
    let cmds = get_script prf in
    let _,_,_,indented_cmds =
      List.fold_left indent_script_item ((1,[]),false,[],[]) cmds
    in
    let indented_cmds = List.rev (indented_cmds) in
    msg_notice (v 0 (Pp.prlist_with_sep Pp.fnl (fun x -> x) indented_cmds))
  with Proof_global.NoCurrentProof -> ()

let () = Vernacentries.show_script := show_script

(* }}} *)

(* vim:set foldmethod=marker: *)
