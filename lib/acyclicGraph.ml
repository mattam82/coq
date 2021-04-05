(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type constraint_type = Le of int | Eq of int (* x =n= y <-> x + n = y *)

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  module IMap : CMap.ExtS with type key = t * int

  module Constraint : CSet.S with type elt = (t * constraint_type * t)

  val source : t
  val equal : t -> t -> bool
  val compare : t -> t -> int

  type explanation = (constraint_type * (t * int)) list
  val error_inconsistency : constraint_type -> t -> t -> explanation lazy_t option -> 'a

  val pr : t -> Pp.t
end

let debug_universes str = ()
  (* Feedback.msg_debug str *)

module Make (Point:Point) = struct

  (* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
  (* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
  (* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
  (* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)
  (* Support for universe polymorphism by MS [2014] *)

  (* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey, Matthieu
     Sozeau, Pierre-Marie Pédrot, Jacques-Henri Jourdan *)

  (* Points are stratified by a partial ordering $\le$.
     Let $\~{}$ be the associated equivalence. We also have a strict ordering
     $<$ between equivalence classes, and we maintain that $<$ is acyclic,
     and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

     At every moment, we have a finite number of points, and we
     maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

     The equivalence $\~{}$ is represented by a tree structure, as in the
     union-find algorithm. The assertions $<$ and $\le$ are represented by
     adjacency lists.

     We use the algorithm described in the paper:

     Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
     new approach to incremental cycle detection and related
     problems. arXiv preprint arXiv:1112.0784.

  *)

  module Index :
  sig
    type t
    val equal : t -> t -> bool
    module Set : CSig.SetS with type elt = t
    module Map : CMap.ExtS with type key = t and module Set := Set
    type table
    val empty : table
    val fresh : Point.t -> table -> t * table
    val fresh_alias : Point.t -> int -> table -> t * table
    val mem : Point.t * int -> table -> bool
    val find : Point.t * int -> table -> t
    val repr : t -> table -> Point.t * int
  end =
  struct
    type t = int
    let equal = Int.equal
    module Set = Int.Set
    module Map = Int.Map

    type table = {
      tab_len : int;
      tab_fwd : (Point.t * int) Int.Map.t;
      tab_bwd : int Point.IMap.t
    }

    let empty = {
      tab_len = 0;
      tab_fwd = Int.Map.empty;
      tab_bwd = Point.IMap.empty;
    }
    let mem x t = Point.IMap.mem x t.tab_bwd
    let find x t = Point.IMap.find x t.tab_bwd
    let repr n t = Int.Map.find n t.tab_fwd

    let fresh x t =
      let () = assert (not @@ mem (x, 0) t) in
      let n = t.tab_len in
      n, {
        tab_len = n + 1;
        tab_fwd = Int.Map.add n (x, 0) t.tab_fwd;
        tab_bwd = Point.IMap.add (x, 0) n t.tab_bwd;
      }

    let fresh_alias x w t =
      let () = assert (mem (x, 0) t) in
      let n = t.tab_len in
      n, {
        tab_len = n + 1;
        tab_fwd = Int.Map.add n (x, w) t.tab_fwd;
        tab_bwd = Point.IMap.add (x, w) n t.tab_bwd;
      }

  end

  module PMap = Index.Map
  module PSet = Index.Set
  module Constraint = Point.Constraint

  type status = NoMark | Visited of int | ToMerge of int

  (** The weights are always non_negative, we use an alias to ensure it *)
  (* type natural = int *)

  (* let natural x =
    assert (0 <= x);
    x *)

  (* Comparison on this type is pointer equality *)
  type canonical_node =
    { canon: Index.t;
      le: PSet.t; (* weak  (le) constraint. *)
      succ: Index.t option; (* Successor *)
      pred : Index.t option; (* Predecessor *)
      ge: PSet.t;
      rank : int;
      klvl: int;
      ilvl: int;
      mutable status: status
    }

  (* A Point.t is either an alias for another one, or a canonical one,
     for which we know the points that are above *)

  type entry =
    | Canonical of canonical_node
    | Equiv of Index.t

  type t =
    { entries : entry PMap.t;
      index : int;
      n_nodes : int; n_edges : int;
      table : Index.table }

  (** Used to cleanup mutable marks if a traversal function is
      interrupted before it has the opportunity to do it itself. *)
  let unsafe_cleanup_marks g =
    let iter _ n = match n with
      | Equiv _ -> ()
      | Canonical n -> n.status <- NoMark
    in
    PMap.iter iter g.entries

  let rec cleanup_marks g =
    try unsafe_cleanup_marks g
    with e ->
      (* The only way unsafe_cleanup_marks may raise an exception is when
         a serious error (stack overflow, out of memory) occurs, or a signal is
         sent. In this unlikely event, we relaunch the cleanup until we finally
         succeed. *)
      cleanup_marks g; raise e

  (* Every Point.t has a unique canonical arc representative *)

  (* Low-level function : makes u an alias for v + weight.
     Does not removes edges from n_edges, but decrements n_nodes.
     u should be entered as canonical before.  *)
  let enter_equiv g u v =
    { entries =
        PMap.modify u (fun _ a ->
            match a with
            | Canonical n ->
              n.status <- NoMark;
              Equiv v
            | _ -> assert false) g.entries;
      index = g.index;
      n_nodes = g.n_nodes - 1;
      n_edges = g.n_edges;
      table = g.table }

  (* Low-level function : changes data associated with a canonical node.
     Resets the mutable fields in the old record, in order to avoid breaking
     invariants for other users of this record.
     n.canon should already been inserted as a canonical node. *)
  let change_node g n =
    { g with entries =
               PMap.modify n.canon
                 (fun _ a ->
                    match a with
                    | Canonical n' ->
                      n'.status <- NoMark;
                      Canonical n
                    | _ -> assert false)
                 g.entries }

  (* canonical representative : we follow the Equiv links *)
  let rec repr g u =
    match PMap.find u g.entries with
    | Equiv v -> repr g v
    | Canonical arc -> arc
    | exception Not_found ->
      CErrors.anomaly ~label:"Univ.repr"
        Pp.(str"Universe " ++ Point.pr (fst (Index.repr u g.table)) ++ str" undefined.")

  let repr_node g ?(w=0) u =
    repr g (Index.find (u, w) g.table)

  exception AlreadyDeclared

  (* Reindexes the given point, using the next available index. *)
  let use_index g u =
    let u = repr g u in
    let g = change_node g { u with ilvl = g.index } in
    assert (g.index > min_int);
    { g with index = g.index - 1 }

  (* Returns 1 if u is higher than v in topological order.
             -1        lower
             0 if u = v *)
  let topo_compare u v =
    if u.klvl > v.klvl then 1
    else if u.klvl < v.klvl then -1
    else if u.ilvl > v.ilvl then 1
    else if u.ilvl < v.ilvl then -1
    else (assert (u==v); 0)

  (* Checks most of the invariants of the graph. For debugging purposes. *)
  let check_invariants ~required_canonical g =
    let required_canonical u = required_canonical (fst (Index.repr u g.table)) in
    let n_edges = ref 0 in
    let n_nodes = ref 0 in
    PMap.iter (fun l u ->
        match u with
        | Canonical u ->
          PSet.iter (fun v ->
              incr n_edges;
              let v = repr g v in
              assert (topo_compare u v = -1);
              if u.klvl = v.klvl then
                assert (PSet.mem u.canon v.ge ||
                        PSet.exists (fun l -> u == repr g l) v.ge))
            u.le;
          PSet.iter (fun v ->
              let v = repr g v in
              assert (v.klvl = u.klvl &&
                      (PSet.mem u.canon v.le ||
                       PSet.exists (fun l -> u == repr g l) v.le))
            ) u.ge;
          assert (u.status = NoMark);
          assert (Index.equal l u.canon);
          assert (u.ilvl > g.index);
          assert (not (PSet.mem u.canon u.le));
          incr n_nodes
        | Equiv _ -> assert (not (required_canonical l)))
      g.entries;
    assert (!n_edges = g.n_edges);
    assert (!n_nodes = g.n_nodes)

  let clean_le g le =
    PSet.fold (fun u acc ->
        let un = repr g u in
        let uu = un.canon in
        if Index.equal uu u then acc
        else (PSet.add uu (PSet.remove u (fst acc)), true))
      le (le, false)

  let clean_gtge g gtge =
    PSet.fold (fun u acc ->
        let un = repr g u in
        let uu = un.canon in
        if Index.equal uu u then acc
        else PSet.add uu (PSet.remove u (fst acc)), true)
      gtge (gtge, false)

  let clean_opt g p =
    Option.Smart.map (fun u -> (repr g u).canon) p

  (* [get_ltle] and [get_gtge] return ltle and gtge arcs.
     Moreover, if one of these lists is dirty (e.g. points to a
     non-canonical node), these functions clean this node in the
     graph by removing some duplicate edges *)
  let get_ltle g u =
    let le, chgt_ltle = clean_le g u.le in
    let succ = clean_opt g u.succ in
    if not chgt_ltle && succ == u.succ then
      u.succ, u.le, u, g
    else
      let sz = PSet.cardinal u.le in
      let sz2 = PSet.cardinal le in
      let u = { u with le; succ } in
      let g = change_node g u in
      let g = { g with n_edges = g.n_edges + sz2 - sz } in
      u.succ, u.le, u, g

  let get_gtge g u =
    let ge, chgt_ge = clean_gtge g u.ge in
    let pred = clean_opt g u.pred in
    if not chgt_ge && pred == u.pred then u.pred, u.ge, u, g
    else
      let u = { u with ge; pred } in
      let g = change_node g u in
      u.pred, u.ge, u, g

  (* [revert_graph] rollbacks the changes made to mutable fields in
     nodes in the graph.
     [to_revert] contains the touched nodes. *)
  let revert_graph to_revert g =
    List.iter (fun t ->
        match PMap.find t g.entries with
        | Equiv _ -> ()
        | Canonical t ->
          t.status <- NoMark) to_revert

  exception AbortBackward of t
  exception CycleDetected

  (* Implementation of the algorithm described in § 5.1 of the following paper:

     Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E. (2011). A
     new approach to incremental cycle detection and related
     problems. arXiv preprint arXiv:1112.0784.

     The "STEP X" comments contained in this file refers to the
     corresponding step numbers of the algorithm described in Section
     5.1 of this paper.  *)

  (* [delta] is the timeout for backward search. It might be
      useful to tune a multiplicative constant. *)
  let get_delta g =
    int_of_float
      (min (float_of_int g.n_edges ** 0.5)
         (float_of_int g.n_nodes ** (2./.3.)))

  let add_opt x s =
    match x with
    | Some x -> PSet.add x s
    | None -> s

  (* x = u, weight = -1, u.ge = [v -> 1, Set -> 1] *)
  let rec backward_traverse to_revert b_traversed count g x =
    let x = repr g x in
    let count = count - 1 in
    if count < 0 then begin
      revert_graph to_revert g;
      raise (AbortBackward g)
    end;
    let visit to_revert =
      x.status <- Visited 0;
      let gt, ge, x, g = get_gtge g x in
      let to_revert, b_traversed, count, g =
        PSet.fold (fun y (to_revert, b_traversed, count, g) ->
            backward_traverse to_revert b_traversed count g y)
          (add_opt gt ge) (to_revert, b_traversed, count, g)
      in
      to_revert, x.canon::b_traversed, count, g
    in
    match x.status with
    (* We might have visited a weaker path before *)
    | NoMark -> visit (x.canon::to_revert)
    | _ -> to_revert, b_traversed, count, g

  let rec forward_traverse f_traversed g v_klvl x y =
    let y = repr g y in
    if y.klvl < v_klvl then begin
      let y = { y with klvl = v_klvl;
                       ge = if x == y then PSet.empty
                         else PSet.singleton x.canon;
                       pred = None }
      in
      let g = change_node g y in
      let lt, le, y, g = get_ltle g y in
      let f_traversed, g =
        PSet.fold (fun z (f_traversed, g) ->
            forward_traverse f_traversed g v_klvl y z)
          (add_opt lt le) (f_traversed, g)
      in
      y.canon::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
          { y with ge = PSet.add x.canon y.ge } in
      f_traversed, g
    else f_traversed, g

  let pr_incr n =
    let open Pp in
    if Int.equal n 0 then mt()
    else if n < 0 then (str" - " ++ int (-n))
    else (str" + " ++ int n)

  let pr_repr_weight g (n, weight) =
    let p, w = (Index.repr n g.table) in
    Pp.(Point.pr p ++ pr_incr (w + weight))
  let pr_can g n =
    let p, w = Index.repr n.canon g.table in
    Pp.(Point.pr p ++ pr_incr w)
  let pr_can_weight g (n, weight) =
    let p, w = Index.repr n.canon g.table in
    Pp.(Point.pr p ++ pr_incr (w + weight))
  let pr_to_merge g =
    Pp.(prlist_with_sep pr_comma (pr_can g))
  let pr_edges g map =
    let fold k acc =
      let vn = repr g k in
      let open Pp in
      hov 2 (str"..." ++ str " <= " ++ pr_can g vn ++ fnl()) ++
      spc () ++ acc
    in
    Index.Set.fold fold map (Pp.mt())

  let pr_edges_inv g map =
  let fold k acc =
    let vn = repr g k in
    let open Pp in
    hov 2 (pr_can g vn ++ str " <= " ++ str"..." ++ fnl()) ++
    spc () ++ acc
  in
  Index.Set.fold fold map (Pp.mt())

  (* Searches for `v` in the predecessors of `u` (recursively x) *)
  let rec find_to_merge to_revert g u v =
    let u = repr g u in
    let visit to_revert =
      if Index.equal u.canon v then
        begin u.status <- ToMerge 0; true, to_revert end
      else
        begin
          debug_universes Pp.(str"In visit to merge, looking at " ++ pr_can g u);
          debug_universes Pp.(str " gtge = " ++ pr_edges_inv g (add_opt u.pred u.ge));
          let merge, to_revert = PSet.fold
              (fun y (merge, to_revert) ->
                let merge', to_revert = find_to_merge to_revert g y v in
                 merge' || merge, to_revert)
                 (add_opt u.pred u.ge) (false, to_revert)
          in
          u.status <- if merge then ToMerge 0 else Visited 0;
          merge, to_revert
        end
    in
    match u.status with
    | NoMark ->
      let to_revert = u::to_revert in
      visit to_revert
    | Visited _ -> false, to_revert
    | ToMerge _ -> true, to_revert

  (* let max_union k w w' = Some (max w w') *)
  (* let min_union k w w' = Some (min w w') *)

  let get_new_edges g succ to_merge =
    (* Computing edge sets. *)
    let lt, le =
      match to_merge with
      | [] -> assert false
      | hd :: tl ->
        let les acc n =
          PSet.union n.le acc
        in
        let le = List.fold_left les hd.le tl in
        let le, _ =  clean_le g le in
        let lts acc n =
          match n.succ with
          | Some succ -> PSet.add succ acc
          | None -> acc
        in
        let lt = List.fold_left lts (Option.cata PSet.singleton PSet.empty hd.succ) tl in
        lt, le
    in
    debug_universes Pp.(str" new le edges: " ++ pr_edges g le);
    debug_universes Pp.(str" new successor edges: " ++ pr_edges g lt);
    let fold accu a =
      if PSet.mem a.canon lt then
        (debug_universes Pp.(str"Cycle detection: positive weight loop on " ++ pr_can g a);
        (* There is a lt edge inside the new component. This is a
            "bad cycle". *)
        raise CycleDetected)
      else if PSet.mem a.canon le then
        PSet.remove a.canon accu
      else accu
    in
    let le = List.fold_left fold le to_merge in
    debug_universes Pp.(str" after checking for cycles: " ++ pr_edges g le);
    let gtge =
      List.fold_left (fun acc n-> PSet.union acc n.ge)
        PSet.empty to_merge
    in
    let gtge, _ = clean_gtge g gtge in
    let gtge = List.fold_left (fun acc n -> PSet.remove n.canon acc) gtge to_merge in
    let lt, lts =
      if PSet.is_empty lt then None, lt
      else (match succ with
        | Some s -> succ, PSet.remove s lt
        | None ->
          let can = PSet.choose lt in
          Some can, PSet.remove can lt)
    in
    (lt, lts, le, gtge)

  let is_to_merge = function
    | ToMerge _ -> true
    | _ -> false

  let get_to_merge u =
    match u.status with
    | ToMerge w -> Some u
    | _ -> None

  let pr_index g i = pr_can g (repr g i)

  let opt_size = function
  | Some _ -> 1
  | None -> 0

  let opt_to_set = function
  | None -> PSet.empty
  | Some v -> PSet.singleton v

  let reorder g u v =
    (* STEP 2: backward search in the k-level of u. *)
    let delta = get_delta g in
    let vn = v in
    debug_universes Pp.(str"reordering: u = " ++
      pr_index g u ++ str" and v = " ++
      pr_index g vn);

    (* [v_klvl] is the chosen future level for u, v and all
        traversed nodes. *)
    let b_traversed, v_klvl, g =
      try
        (* If backward search succeeds then we have paths from the nodes of b_traversered to u *)
        let to_revert, b_traversed, _, g = backward_traverse [] [] delta g u in
        revert_graph to_revert g;
        let v_klvl = (repr g u).klvl in
        b_traversed, v_klvl, g
      with AbortBackward g ->
        (* Backward search was too long, use the next k-level. *)
        let v_klvl = (repr g u).klvl + 1 in
        [], v_klvl, g
    in
    let f_traversed, g =
      (* STEP 3: forward search. Contrary to what is described in
          the paper, we do not test whether v_klvl = u.klvl nor we assign
          v_klvl to v.klvl. Indeed, the first call to forward_traverse
          will do all that. *)
      let vn = repr g v in
      forward_traverse [] g v_klvl vn v
    in

    (* STEP 4: merge nodes if needed. *)
    let to_merge, b_reindex, f_reindex =
      if (repr g u).klvl = v_klvl then
        begin
          let merge, to_revert = find_to_merge [] g u v in
          let r =
            if merge then
              List.filter_map (fun u -> get_to_merge u) to_revert,
              List.filter (fun u -> not (is_to_merge (repr g u).status)) b_traversed,
              List.filter (fun u -> not (is_to_merge (repr g u).status)) f_traversed
            else [], b_traversed, f_traversed
          in
          List.iter (fun u -> u.status <- NoMark) to_revert;
          r
        end
      else [], b_traversed, f_traversed
    in
    let () =
      debug_universes Pp.(str"Found to merge: " ++ hov 0 (pr_to_merge g to_merge))
    in
    let to_reindex, g =
      match to_merge with
      | [] -> List.rev_append f_reindex b_reindex, g
      | n0::q0 ->
        (* Computing new root. *)
        let root, rank_rest =
          List.fold_left (fun ((best, _rank_rest) as acc) n ->
              if n.rank >= best.rank then n, best.rank else acc)
            (n0, min_int) q0
        in
        debug_universes Pp.(str"Chosen new root: " ++ pr_can g root);
        let succ, lts, le, ge = get_new_edges g root.succ to_merge in
        (* Inserting the new root. *)
        debug_universes Pp.(str"Inserting new root with edges: le = " ++ pr_edges g le ++ spc () ++ str " ge = " ++ pr_edges_inv g ge
          ++ str" succ = " ++ pr_edges g (opt_to_set succ));
        let g = change_node g
            { root with le; ge; succ;
                        rank = max root.rank (rank_rest + 1); }
        in
        let lts' = List.map (repr g) (PSet.elements lts) in
        debug_universes Pp.(str"Successors to update: " ++ pr_to_merge g lts');
        (* Inserting shortcuts for old nodes. *)
        let g = List.fold_left (fun g n ->
            if Index.equal n.canon root.canon then g
            else
              (debug_universes Pp.(str"Inserting equivalence : " ++ pr_can g n ++
              str " = " ++ pr_can g root);
              enter_equiv g n.canon root.canon))
            g to_merge
        in

        (* Updating g.n_edges *)
        let oldsz =
          List.fold_left (fun sz u -> sz+PSet.cardinal u.le)
            0 to_merge
        in
        let sz = PSet.cardinal le + opt_size succ + PSet.cardinal lts in
        let g = { g with n_edges = g.n_edges + sz - oldsz } in

        (* Not clear in the paper: we have to put the newly
            created component just between B and F. *)
        List.rev_append f_reindex (root.canon::b_reindex), g

    in

    (* STEP 5: reindex traversed nodes. *)
    List.fold_left use_index g to_reindex

  (* Assumes [u] and [v] are already in the graph. *)
  (* Does NOT assume that ucan != vcan. *)
  let insert_le ucan vcan g =
    try
      let u = ucan.canon and v = vcan.canon in
      (* STEP 1: do we need to reorder nodes ? *)
      let g = if topo_compare ucan vcan <= 0 then g else reorder g u v in

      (* STEP 6: insert the new edge in the graph. *)
      let u = repr g u in
      let v = repr g v in
      if u == v then g
      else
        let g =
          if PSet.mem v.canon u.le then g
          else { (change_node g { u with le = PSet.add v.canon u.le })
              with n_edges = g.n_edges + 1 }
        in
        if u.klvl <> v.klvl || PSet.mem u.canon v.ge then g
        else
          let v = { v with ge = PSet.add u.canon v.ge } in
          change_node g v
    with
    | CycleDetected as e -> raise e
    | e ->
      (* Unlikely event: fatal error or signal *)
      let () = cleanup_marks g in
      raise e

  (*let rec insert_eq ucan vcan g =
    if ucan == vcan then g
    else let g = insert_le ucan vcan g in
      insert_le vcan ucan g

  and insert_le ucan vcan g =
    let g, succ = insert_le_succ ucan vcan g in
    match succ with
    | None -> g
    | Some (succ, succs) ->
      List.fold_right (insert_eq (repr g succ)) succs g*)

  let add_node ?(rank=0) ?succ ?pred v g =
    let klvl = match pred with Some u -> (repr g u).klvl + 1 | None -> 0 in
    let node = {
      canon = v;
      le = PSet.empty;
      succ;
      ge = PSet.empty;
      pred;
      rank;
      klvl;
      ilvl = g.index;
      status = NoMark;
    }
    in
    let entries = PMap.add v (Canonical node) g.entries in
    { entries; index = g.index - 1; n_nodes = g.n_nodes + 1;
      n_edges = g.n_edges + opt_size succ + opt_size pred; table = g.table }, node

  let add ?(rank=0) ?pred v g =
    if Index.mem (v,0) g.table then raise AlreadyDeclared
    else
      let () = assert (g.index > min_int) in
      let v, table = Index.fresh v g.table in
      let pred = Option.map (fun p -> Index.find (p, 0) table) pred in
      let g, node = add_node ~rank ?pred v { g with table } in
      match pred with
      | None -> g
      | Some pred ->
        change_node g { (repr g pred) with succ = Some node.canon }

  exception Undeclared of Point.t
  let check_declared g us =
    let check l = if not (Index.mem (l, 0) g.table) then raise (Undeclared l) in
    Point.Set.iter check us

  exception Found_explanation of (constraint_type * (Point.t * int)) list

  let repr_expl_left g idx =
    let can = repr g idx in
    let expl =
      if can.canon == idx then []
      else
        let p, w = Index.repr can.canon g.table in
        [(Eq 0, (p, w))]
    in
    can, expl
  let repr_expl_right g idx =
    let can = repr g idx in
    let expl =
      if can.canon == idx then None
      else
        let p, w = Index.repr idx g.table in
        Some (p, w)
    in
    can, expl

  let get_explanation u v weight g =
    let vidx = Index.find (v, 0) g.table in
    let uidx = Index.find (u, 0) g.table in
    (let vp = v in debug_universes Pp.(str "Looking for path from: " ++ Point.pr u ++ str " to " ++ Point.pr vp ++ str " of weight " ++
     pr_incr weight));
    let v, explv = repr_expl_left g vidx in
    let visited_strict = ref PMap.empty in
    let rec traverse weight u =
      if u == v then
        (debug_universes Pp.(str "found: " ++ pr_can_weight g (u, 0) ++ str " weight is" ++ pr_incr weight);
        if weight >= 0 then Some [] else None)
      else if topo_compare u v = 1 then None
      else
        let visited =
          (* Did we already visit this node through a path of larger weight? *)
          try (PMap.find u.canon !visited_strict >= weight)
          with Not_found -> false
        in
        if visited then None
        else begin
          visited_strict := PMap.add u.canon 0 !visited_strict;
          try
            let visit weight u' =
              debug_universes Pp.(str "traversing: " ++ pr_repr_weight g (u', 0) ++ str" weight is " ++ int weight);
              let canu', explu' = repr_expl_right g u' in
              match traverse weight canu' with
              | None -> ()
              | Some exp ->
                let pu'', wu'' = Index.repr canu'.canon g.table in
                let typ = Le weight in
                let expleq =
                  match explu' with
                  | None -> (typ, (pu'', wu'')) :: exp
                  | Some (pu', wu') -> (typ, (pu', wu')) :: (Eq 0, (pu'', wu'')) :: exp
                in
                raise (Found_explanation expleq)
            in
            Option.iter (visit 1) u.succ;
            PSet.iter (visit 0) u.le;
            None
          with Found_explanation exp -> Some exp
        end
    in
    let u, explu = repr_expl_left g uidx in
    let make_expl exp =
      List.append explu (List.append exp explv)
    in
    if u == v then
      let p, w = Index.repr v.canon g.table in
      make_expl [Eq 0, (p, w)]
    else match traverse weight u with Some exp -> make_expl exp | None -> assert false

  let get_explanation u v vn g =
    Some (lazy (get_explanation u v vn g))

  (* To compare two nodes, we simply do a forward search.
     We implement two improvements:
     - we ignore nodes that are higher than the destination;
     - we do a BFS rather than a DFS because we expect to have a short
         path (typically, the shortest path has length 1)
  *)
  exception Found of canonical_node list
  let search_path weight u v g =
    let rec loop to_revert todo next_todo =
      match todo, next_todo with
      | [], [] -> to_revert (* No path found *)
      | [], _ -> loop to_revert next_todo []
      | (u, weight)::todo, _ ->
        match u.status with
        | Visited w when w >= weight ->
         loop to_revert todo next_todo
        | _ ->
          let to_revert =
            if u.status = NoMark then u::to_revert else to_revert
          in
          u.status <- Visited weight;
          if PSet.mem v.canon u.le then raise (Found to_revert)
          else
            begin
              let visit weight u next_todo =
                let u = repr g u in
                if u == v && weight >= 0 then raise (Found to_revert)
                else if topo_compare u v = 1 then next_todo
                else (u, weight)::next_todo
              in
              let next_todo =
                PSet.fold (visit weight) u.le (Option.fold_right (visit (succ weight)) u.succ next_todo)
              in
              loop to_revert todo next_todo
            end
    in
    if u == v then weight <= 0
    else
      try
        let res, to_revert =
          try false, loop [] [u, weight] []
          with Found to_revert -> true, to_revert
        in
        List.iter (fun u -> u.status <- NoMark) to_revert;
        res
      with e ->
        (* Unlikely event: fatal error or signal *)
        let () = cleanup_marks g in
        raise e

  (** Uncomment to debug the cycle detection algorithm. *)
  (*let insert_edge strict ucan vcan g =
    let check_invariants = check_invariants ~required_canonical:(fun _ -> false) in
    check_invariants g;
    let g = insert_edge strict ucan vcan g in
    check_invariants g;
    let ucan = repr g ucan.canon in
    let vcan = repr g vcan.canon in
    assert (search_path strict ucan vcan g);
    g*)

  (** User interface *)

  type 'a check_function = t -> 'a -> int -> 'a -> bool

  let check_eq g u w v =
    u == v ||
    let arcu = repr_node g ~w u and arcv = repr_node g v in
    arcu == arcv

  let check_smaller g weight u v =
    let u = repr_node g u in
    let v = repr_node g v in
    search_path weight u v g

  let check_leq g u n v = check_smaller g n u v

  let fresh_alias g p w =
    let idx, table = Index.fresh_alias p w g.table in
    { g with table }, idx

  let find_alias g p w =
    Index.find (p, w) g.table

  (* let insert_successor_edge w u v g =
    if w <= 0 then g
    else (match u.succ with
      | Some succ ->
        aux (w - 1) (repr g succ) v g
      | None -> g) *)

  (* let insert_edge_le u v g =
    let rec aux w u v g =
      (let vn = v in
      debug_universes Pp.(str"Inserting edge : " ++ pr_can g u ++pr_incr w ++ str" <= " ++ pr_can g vn));
      let g = insert_edge w u v g in
      if w <= 0 then g
      else (match u.succ with
        | Some succ ->
          debug_universes Pp.(str"Found successor");
          aux (w - 1) (repr g succ) v g
        | None -> g)
    in aux w u v g *)

  let rec find_succ g (p, w) u k =
    match u.succ with
    | Some s ->
      if k = 1 then g, repr g s
      else (* w > 1 *)
        find_succ g (p, w + 1) (repr g s) (k - 1)
    | None ->
      let g, u' = fresh_alias g p (w + 1) in
      let g, canu' = add_node u' ~pred:u.canon g in
      let u = { u with succ = Some canu'.canon } in
      let g = change_node g u in
      debug_universes Pp.(str"Inserted edge : " ++ pr_can_weight g (u, 0) ++ str" <= " ++
        pr_can_weight g (canu', 0));
      let g = { g with n_nodes = g.n_nodes + 1; n_edges = g.n_edges + 2 } in
      find_succ g (p, w) u k
  let rec find_pred g (p, w) u k =
    match u.pred with
    | Some s ->
      if k = -1 then g, repr g s
      else (* w > 1 *)
        find_pred g (p, w - 1) (repr g s) (k + 1)
    | None ->
      let g, u' = fresh_alias g p (w - 1) in
      let g, canu' = add_node u' ~succ:u.canon g in
      let u = { u with pred = Some canu'.canon } in
      let g = change_node g u in
      debug_universes Pp.(str"Inserted edge : " ++ pr_can_weight g (u, 0) ++ str" <= " ++
        pr_can_weight g (canu', 0));
      let g = { g with n_nodes = g.n_nodes + 1; n_edges = g.n_edges + 2 } in
      find_pred g (p, w) u k

  let find_successor g u w =
    debug_universes Pp.(str"Making successor of : " ++ pr_can_weight g (u, 0) ++ str " of weight " ++ pr_incr w);
    let p, w' = Index.repr u.canon g.table in
    try
      let u' = find_alias g p (w + w') in
      g, repr g u'
    with Not_found -> find_succ g (p, w') u w
  let _find_predecessor g u w =
    debug_universes Pp.(str"Making predecessor of : " ++ pr_can_weight g (u, 0) ++ str " of weight " ++ pr_incr w);
    let p, w' = Index.repr u.canon g.table in
    try
      let u' = find_alias g p (w + w') in
      g, repr g u'
    with Not_found -> find_pred g (p, w') u w

  let merge_successors g =
    let rec find_next_succ g orig dest x =
      let x = repr g x in
      let lt, le, x, g = get_ltle g x in
      match lt with
      | Some succ' ->
        let succ' = repr g succ' in
        (* debug_universes (Pp.(str"merge_successors: found following successor of " ++ pr_index g orig  ++ str " -> " ++ pr_index g dest ++
          str" " ++ pr_can g x ++ str" successor: " ++ pr_can g succ')); *)
        if search_path 0 succ' (repr g dest) g then
          (* (debug_universes (Pp.(str"merge_successors: found path between " ++ pr_can g succ'  ++ str " and " ++
          pr_index g orig)); *)
          let g = insert_le x (repr g orig) g in
          insert_le (repr g dest) succ' g
        else g
          (* (debug_universes (Pp.(str"merge_successors: no path between " ++ pr_can g succ'  ++ str " and " ++
          pr_index g orig)); *)
      | None ->
        PSet.fold (fun succ' g ->
          find_next_succ g orig dest succ') le g
    and visit x g =
      let xcan = repr g x in
      let lt, le, xcan, g = get_ltle g xcan in
      match lt with
      | Some succ ->
        (* debug_universes
        (Pp.(str"merge_successors: found succ " ++ pr_can g xcan  ++ str " -> " ++ pr_index g succ)); *)
        (* x has a direct successor, we need to merge all intermediate universes
           that participate in any other positive weight path from x to its successor *)
          PSet.fold (fun succ' g ->
            find_next_succ g x succ succ') le g
      | None ->
        PSet.fold visit le g
    in
    let src = Index.find (Point.source, 0) g.table in
    visit src g

  (* Look for any successor above v and set u <= v to ensure upper bounds are respected *)
  let _saturate_successors u v g =
    let v = repr g v.canon in
    PSet.fold (fun vnext g ->
      insert_le u (repr g vnext) g) v.le g

  (* insert_edge u w v adds an edge u + w <= v *)
  let insert_edge w u v g =
    debug_universes (let vn = v in
    Pp.(str"Inserting edge of weight " ++ int w ++ str " between " ++
    pr_can_weight g (u, 0) ++ str" and " ++ pr_can_weight g (vn, 0)));
    if w = 0 then insert_le u v g
    else if w < 0 then
      (* If we want to insert an arc of positive or negative weight, we rather make an alias
        u' of u + w and replace u with u' + w everywhere. Then we can add u' <= v.
      *)
      (let g, canv' = find_successor g v (-w) in
      debug_universes Pp.(str"Alias represents " ++ pr_can g canv');
      insert_le u canv' g)
    else
      (let g, canu' = find_successor g u w in
      debug_universes Pp.(str"Alias represents " ++ pr_can g canu');
      insert_le canu' v g)

  let insert_edge w u v g =
    merge_successors (insert_edge w u v g)

  (* enforce_eq g u n v will force u + n = v if possible, will fail otherwise *)

  let enforce_eq u n v g =
    let ucan = repr_node g u in
    let vcan = repr_node g v in
    if ucan == vcan then
      if Int.equal n 0 then g
      else Point.error_inconsistency (Eq n) u v None
    else if topo_compare ucan vcan = 1 then
      let g = insert_edge (-n) vcan ucan g in  (* Cannot fail *)
      try insert_edge n ucan vcan g
      with CycleDetected ->
        Point.error_inconsistency (Eq (- n)) v u (get_explanation v u (n) g)
    else
      let g = insert_edge n ucan vcan g in  (* Cannot fail *)
      try insert_edge (-n) vcan ucan g
      with CycleDetected ->
        Point.error_inconsistency (Eq (-n)) v u (get_explanation u v (-n) g)

  (* enforce_leq g u v will force u<=v if possible, will fail otherwise *)
  let enforce_leq u n v g =
    let ucan = repr_node g u in
    let vcan = repr_node g v in
    try insert_edge n ucan vcan g
    with CycleDetected ->
      Point.error_inconsistency (Le n) u v (get_explanation v u (succ n) g)

  (* enforce_lt u v will force u<v if possible, will fail otherwise *)
  (* let enforce_lt u v g =
    let ucan, weightu = repr_node g u in
    let vcan, weightv = repr_node g v in
    try insert_edge (1 + weightu - weightv) ucan vcan g
    with CycleDetected ->
      Point.error_inconsistency (Le 1) u v (get_explanation (-1) v u g) *)

  let empty =
    { entries = PMap.empty; index = 0; n_nodes = 0; n_edges = 0; table = Index.empty }

  (* Normalization *)

  let constraints_of g =
    let module UF = Unionfind.Make (Point.Set) (Point.Map) in
    let uf = UF.create () in
    let constraints_of u v acc =
      match v with
      | Canonical {canon=u; le; succ; _} ->
        let visit weight v acc =
          let u, uw = Index.repr u g.table in
          let v, vw = Index.repr v g.table in
          let typ = Le (uw - vw + weight) in
          Constraint.add (u,typ,v) acc
        in
        PSet.fold (visit 0) le (Option.fold_right (visit 1) succ acc)
      | Equiv v ->
        let u, uw = Index.repr u g.table in
        let v, vw = Index.repr v g.table in
        if uw == vw then UF.union u v uf; acc
    in
    let csts = PMap.fold constraints_of g.entries Constraint.empty in
    csts, UF.partition uf

  let add_weights uv vw = function
    | Eq n -> Eq (uv - vw + n)
    | Le n -> Le (uv - vw + n)

  (* domain g.entries = kept + removed *)
  let constraints_for ~kept g =
    (* rmap: partial map from canonical points to kept points *)
    let add_cst u knd v cst =
      let u, uw = Index.repr u g.table in
      let v, vw = Index.repr v g.table in
      Constraint.add (u, add_weights uw vw knd, v) cst
    in
    let kept = Point.Set.fold (fun u accu -> PSet.add (Index.find (u,0) g.table) accu) kept PSet.empty in
    let rmap, csts = PSet.fold (fun u (rmap,csts) ->
        let arcu = repr g u in
        if PSet.mem arcu.canon kept then
          let csts = if Index.equal u arcu.canon then csts
            else add_cst u (Eq 0) arcu.canon csts
          in
          PMap.add arcu.canon arcu.canon rmap, csts
        else
          match PMap.find arcu.canon rmap with
          | v -> rmap, add_cst u (Eq 0) v csts
          | exception Not_found -> PMap.add arcu.canon u rmap, csts)
        kept (PMap.empty,Constraint.empty)
    in
    let rec add_from u csts todo = match todo with
      | [] -> csts
      | (v,weight)::todo ->
        let v = repr g v in
        (match PMap.find v.canon rmap with
         | v ->
           let d = Le 0 in
           let csts = add_cst u d v csts in
           add_from u csts todo
         | exception Not_found ->
           (* v is not equal to any kept point *)
           let todo = Option.fold_right (fun v' todo -> (v', succ weight) :: todo) v.succ todo in
           let todo = PSet.fold (fun v' todo -> (v', weight) :: todo) v.le todo in
           add_from u csts todo)
    in
    PSet.fold (fun u csts ->
        let ru = repr g u in
        let csts = Option.fold_right (fun v csts -> add_from u csts [v, 1]) ru.succ csts in
        PSet.fold (fun v csts -> add_from u csts [v,0]) ru.le csts)
      kept csts

  let domain g =
    let fold u _ accu = Point.Set.add (fst (Index.repr u g.table)) accu in
    PMap.fold fold g.entries Point.Set.empty

  let choose p g u =
    let exception Found of Point.t in
    let ru = repr_node g u in
    let ru = ru.canon in
    let ruv, ruvw = Index.repr ru g.table in
    if p ruv then Some ruv
    else
      try PMap.iter (fun v -> function
          | Canonical _ -> () (* we already tried [p ru] *)
          | Equiv v' ->
            let rv = repr g v' in
            let rv = rv.canon in
            if rv == ru then
              let v, _vw = Index.repr v g.table in
              if p v then raise (Found v)
            (* NB: we could also try [p v'] but it will come up in the
               rest of the iteration regardless. *)
        ) g.entries; None
      with Found v -> Some v

  type node = Alias of Point.t * int | Node of int Point.IMap.t * Point.Set.t
  type repr = node Point.IMap.t

  let repr g =
    let fold u n accu =
      let pu, uw = Index.repr u g.table in
      let n = match n with
      | Canonical n ->
        let fold w v accu =
          let v, vw = Index.repr v g.table in
          Point.IMap.add (v, vw) w accu in
        let ltle = PSet.fold (fold 0) n.le Point.IMap.empty in
        let ltle = Option.fold_right (fold 1) n.succ ltle in
        let fold u accu = Point.Set.add (fst (Index.repr u g.table)) accu in
        let gtge = PSet.fold fold n.ge Point.Set.empty in
        Node (ltle, gtge)
      | Equiv v ->
        let v, vw = Index.repr v g.table in
        Alias (v, vw)
      in
      Point.IMap.add (pu, uw) n accu
    in
    PMap.fold fold g.entries Point.IMap.empty

end
