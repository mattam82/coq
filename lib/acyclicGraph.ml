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

  type explanation = (constraint_type * t) list
  val error_inconsistency : constraint_type -> t -> t -> explanation lazy_t option -> 'a

  val pr : t -> Pp.t
end

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
      let () = assert (mem (x, w) t) in
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
  type natural = int

  (* let natural x =
    assert (0 <= x);
    x *)

  (* Comparison on this type is pointer equality *)
  type canonical_node =
    { canon: Index.t;
      ltle: natural PMap.t;  (* canon + n <= x
            > 0: strict (lt) constraint.
            = 0: weak  (le) constraint. *)
      gtge: PSet.t;
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

  let shift_pmap k m =
    PMap.map (fun weight -> weight + k) m

  let repr_ltle (arc, w) =
    if Int.equal w 0 then arc.ltle
    else shift_pmap w arc.ltle

  (* let repr_gtge (arc, w) =
    if Int.equal w 0 then arc.gtge
    else shift_pmap (- w) arc.gtge  *)

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
          PMap.iter (fun v _strict ->
              incr n_edges;
              let v, vw = repr g v in
              assert (topo_compare u v = -1);
              if u.klvl = v.klvl then
                assert (PSet.mem u.canon v.gtge ||
                        PSet.exists (fun l -> u == fst (repr g l)) v.gtge))
            u.ltle;
          PSet.iter (fun v ->
              let v, vw = repr g v in
              assert (v.klvl = u.klvl &&
                      (PMap.mem u.canon v.ltle ||
                       PMap.exists (fun l _ -> u == fst (repr g l)) v.ltle))
            ) u.gtge;
          assert (u.status = NoMark);
          assert (Index.equal l u.canon);
          assert (u.ilvl > g.index);
          assert (not (PMap.mem u.canon u.ltle));
          incr n_nodes
        | Equiv _ -> assert (not (required_canonical l)))
      g.entries;
    assert (!n_edges = g.n_edges);
    assert (!n_nodes = g.n_nodes)

  let add_pmap_min u weightu v map =
    match PMap.find v map with
    | exception Not_found -> PMap.add u weightu map
    | weightv -> PMap.add u (min weightu weightv) (PMap.remove v map)

  let clean_ltle g ltle =
    PMap.fold (fun u weight acc ->
        let un, weight = repr_weight g u (-weight) in
        let uu = un.canon in
        if Index.equal uu u then acc
        else (add_pmap_min uu weight u (fst acc), true))
      ltle (ltle, false)

  let clean_gtge g gtge =
    PSet.fold (fun u acc ->
        let un, weightun = repr g u in
        let uu = un.canon in
        if Index.equal uu u then acc
        else PSet.add uu (PSet.remove u (fst acc)), true)
      gtge (gtge, false)

  (* [get_ltle] and [get_gtge] return ltle and gtge arcs.
     Moreover, if one of these lists is dirty (e.g. points to a
     non-canonical node), these functions clean this node in the
     graph by removing some duplicate edges *)
  let get_ltle g u =
    let ltle, chgt_ltle = clean_ltle g u.ltle in
    if not chgt_ltle then u.ltle, u, g
    else
      let sz = PMap.cardinal u.ltle in
      let sz2 = PMap.cardinal ltle in
      let u = { u with ltle } in
      let g = change_node g u in
      let g = { g with n_edges = g.n_edges + sz2 - sz } in
      u.ltle, u, g

  let get_gtge g u =
    let gtge, chgt_gtge = clean_gtge g u.gtge in
    if not chgt_gtge then u.gtge, u, g
    else
      let u = { u with gtge } in
      let g = change_node g u in
      u.gtge, u, g

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

  (* x = u, weight = -1, u.gtge = [v -> 1, Set -> 1] *)
  let rec backward_traverse to_revert b_traversed count g x =
    let x, weight = repr g x in
    let count = count - 1 in
    if count < 0 then begin
      revert_graph to_revert g;
      raise (AbortBackward g)
    end;
    let visit to_revert =
      x.status <- Visited weight;
      let gtge, x, g = get_gtge g x in
      let to_revert, b_traversed, count, g =
        PSet.fold (fun y (to_revert, b_traversed, count, g) ->
            backward_traverse to_revert b_traversed count g y)
          gtge (to_revert, b_traversed, count, g)
      in
      to_revert, PMap.add x.canon weight b_traversed, count, g
    in
    match x.status with
    (* We might have visited a weaker path before *)
    | Visited w when w < weight -> visit to_revert
    | NoMark -> visit (x.canon::to_revert)
    | _ -> to_revert, b_traversed, count, g

  let rec forward_traverse f_traversed g v_klvl x y =
    let y, weighty = repr g y in
    if y.klvl < v_klvl then begin
      let y = { y with klvl = v_klvl;
                       gtge = if x == y then PSet.empty
                         else PSet.singleton x.canon }
      in
      let g = change_node g y in
      let ltle, y, g = get_ltle g y in
      let f_traversed, g =
        PMap.fold (fun z weightz (f_traversed, g) ->
            forward_traverse f_traversed g v_klvl y z)
          ltle (f_traversed, g)
      in
      y.canon::f_traversed, g
    end else if y.klvl = v_klvl && x != y then
      let g = change_node g
          { y with gtge = PSet.add x.canon y.gtge } in
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
  let pr_can_weight g (n, weight) =
    let p, w = Index.repr n.canon g.table in
    Pp.(Point.pr p ++ pr_incr (w + weight))
  let pr_to_merge g =
    Pp.(prlist_with_sep pr_comma (pr_can_weight g))
  let pr_edges g map =
    let open Pp in
    let fold k weight acc =
      let v = repr_weight g k 0 in
      hov 2 (str"..." ++ pr_incr weight ++ str " <= " ++ pr_can_weight g v ++ fnl()) ++
      spc () ++ acc
    in
    Index.Map.fold fold map (mt())

  let pr_edges_inv g map =
      let open Pp in
      let fold k acc =
        let v = repr_weight g k 0 in
        hov 2 (pr_can_weight g v ++ str " <= " ++ str"..." ++ fnl()) ++
        spc () ++ acc
      in
      Index.Set.fold fold map (mt())

  (* Searches for `v` in the predecessors of `u` (recursively x) *)
  let rec find_to_merge to_revert g u v =
    let u, weight = repr g u in
    let visit to_revert =
      if Index.equal u.canon v then
        begin u.status <- ToMerge weight; true, to_revert end
      else
        begin
          Feedback.msg_debug Pp.(str"In visit to merge, looking at " ++ pr_can_weight g (u, weight));
          Feedback.msg_debug Pp.(str " gtge = " ++ pr_edges_inv g u.gtge);
          let merge, to_revert = PSet.fold
              (fun y (merge, to_revert) ->
                let merge', to_revert = find_to_merge to_revert g y v in
                 merge' || merge, to_revert) u.gtge (false, to_revert)
          in
          u.status <- if merge then ToMerge weight else Visited weight;
          merge, to_revert
        end
    in
    match u.status with
    | NoMark ->
      let to_revert = u::to_revert in
      visit to_revert
    | Visited w when w <= weight -> visit to_revert
    | ToMerge w when w < weight -> visit to_revert
    | ToMerge _ -> true, to_revert
    | _ -> false, to_revert

  (* let max_union k w w' = Some (max w w') *)
  (* let min_union k w w' = Some (min w w') *)

  let get_new_edges g weight to_merge =
    (* Computing edge sets. *)
    let ltle =
      let fold acc (n, weightn) =
        let fold u weightu acc =
          match PMap.find u acc with
          | n -> (* Already a path from the component to u *)
            if n >= weightu then acc
            else PMap.add u weightu acc
          | exception Not_found -> PMap.add u weightu acc
        in
        PMap.fold fold (shift_pmap weightn n.ltle) acc
      in
      match to_merge with
      | [] -> assert false
      | (hd, weighthd) :: tl -> List.fold_left fold (shift_pmap weighthd hd.ltle) tl
    in
    let ltle, _ = clean_ltle g ltle in
    Feedback.msg_debug Pp.(str" new edges: " ++ pr_edges g ltle);
    let fold accu (a, weighta) =
      match PMap.find a.canon ltle with
      | n ->
        Feedback.msg_debug Pp.(str"Cycle detection: " ++
          pr_can_weight g (a, n) ++ str " <= " ++ pr_can_weight g (a, weighta));
        (* There is a lt edge inside the new component. This is a
            "bad cycle". *)
        if n > weighta then raise CycleDetected
        else PMap.remove a.canon accu
      | exception Not_found -> accu
    in
    let ltle = List.fold_left fold ltle to_merge in
    Feedback.msg_debug Pp.(str" after checking for cycles: " ++ pr_edges g ltle);
    let gtge =
      List.fold_left (fun acc (n, weight) -> PSet.union acc n.gtge)
        PSet.empty to_merge
    in
    let gtge, _ = clean_gtge g gtge in
    let gtge = List.fold_left (fun acc (n, _) -> PSet.remove n.canon acc) gtge to_merge in
    (ltle, gtge)

  let is_to_merge = function
    | ToMerge _ -> true
    | _ -> false

  let get_to_merge u =
    match u.status with
    | ToMerge w -> Some (u, w)
    | _ -> None

  let reorder g u v =
    (* STEP 2: backward search in the k-level of u. *)
    let delta = get_delta g in
    let vn = v in
    Feedback.msg_debug Pp.(str"reordering: u = " ++
      pr_can_weight g (repr_weight g u 0) ++ str" and v = " ++
      pr_can_weight g (repr_weight g vn 0));

    (* [v_klvl] is the chosen future level for u, v and all
        traversed nodes. *)
    let b_traversed, v_klvl, g =
      try
        (* If backward search succeeds then we have paths from the nodes of b_traversered to u *)
        let to_revert, b_traversed, _, g = backward_traverse [] PMap.empty delta g u in
        revert_graph to_revert g;
        let v_klvl = (fst (repr g u)).klvl in
        b_traversed, v_klvl, g
      with AbortBackward g ->
        (* Backward search was too long, use the next k-level. *)
        let v_klvl = (fst (repr g u)).klvl + 1 in
        PMap.empty, v_klvl, g
    in
    let f_traversed, g =
      (* STEP 3: forward search. Contrary to what is described in
          the paper, we do not test whether v_klvl = u.klvl nor we assign
          v_klvl to v.klvl. Indeed, the first call to forward_traverse
          will do all that. *)
      let vn, weightv = repr g v in
      forward_traverse [] g v_klvl vn v
    in

    (* STEP 4: merge nodes if needed. *)
    let to_merge, b_reindex, f_reindex =
      let b_traversed = PSet.elements (PMap.domain b_traversed) in
      if (fst (repr g u)).klvl = v_klvl then
        begin
          let merge, to_revert = find_to_merge [] g u v in
          let r =
            if merge then
              List.filter_map (fun u -> get_to_merge u) to_revert,
              List.filter (fun u -> not (is_to_merge (fst (repr g u)).status)) b_traversed,
              List.filter (fun u -> not (is_to_merge (fst (repr g u)).status)) f_traversed
            else [], b_traversed, f_traversed
          in
          List.iter (fun u -> u.status <- NoMark) to_revert;
          r
        end
      else [], b_traversed, f_traversed
    in
    let () =
      Feedback.msg_debug Pp.(str"Found to merge: " ++ hov 0 (pr_to_merge g to_merge))
    in
    let to_reindex, g =
      match to_merge with
      | [] -> List.rev_append f_reindex b_reindex, g
      | n0::q0 ->
        (* Computing new root. *)
        let (root, weight), rank_rest =
          List.fold_left (fun (((best, _bestweight), _rank_rest) as acc) (n, weight as node) ->
              if n.rank >= best.rank then node, best.rank else acc)
            (n0, min_int) q0
        in
        Feedback.msg_debug Pp.(str"Chosen new root: " ++ pr_can_weight g (root, weight));
        let ltle, gtge = get_new_edges g weight to_merge in
        (* Inserting the new root. *)
        Feedback.msg_debug Pp.(str"Inserting new root with edges: ltle = " ++ pr_edges g ltle ++ spc () ++ str " gtge = " ++ pr_edges_inv g gtge);
        let g = change_node g
            { root with ltle; gtge;
                        rank = max root.rank (rank_rest + 1); }
        in

        (* Inserting shortcuts for old nodes. *)
        let g = List.fold_left (fun g (n, weightn) ->
            if Index.equal n.canon root.canon then g else
              (Feedback.msg_debug Pp.(str"Inserting equivalence : " ++ pr_can_weight g (n, 0) ++ str " = root + " ++ int (weight - weightn));
              enter_equiv g n.canon (weight - weightn) root.canon))
            g to_merge
        in

        (* Updating g.n_edges *)
        let oldsz =
          List.fold_left (fun sz u -> sz+PMap.cardinal (fst u).ltle)
            0 to_merge
        in
        let sz = PMap.cardinal ltle in
        let g = { g with n_edges = g.n_edges + sz - oldsz } in

        (* Not clear in the paper: we have to put the newly
            created component just between B and F. *)
        List.rev_append f_reindex (root.canon::b_reindex), g

    in

    (* STEP 5: reindex traversed nodes. *)
    List.fold_left use_index g to_reindex

  (* Assumes [u] and [v] are already in the graph. *)
  (* Does NOT assume that ucan != vcan. *)
  let insert_edge weight ucan vcan g =
    try
      let u = ucan.canon and v = vcan.canon in
      (* STEP 1: do we need to reorder nodes ? *)
      let g = if topo_compare ucan vcan <= 0 then g else reorder g u v in

      (* STEP 6: insert the new edge in the graph. *)
      let u, weightu = repr_weight g u weight in
      let v, weightv = repr g v in
      let weight = weightu - weightv in
      if u == v then
        if weight > 0 then raise CycleDetected else g
      else
        let g =
          try let oldweight = PMap.find v.canon u.ltle in
            if weight > oldweight then
              change_node g { u with ltle = PMap.add v.canon weight u.ltle }
            else g
          with Not_found ->
            { (change_node g { u with ltle = PMap.add v.canon weight u.ltle })
              with n_edges = g.n_edges + 1 }
        in
        if u.klvl <> v.klvl || PSet.mem u.canon v.gtge then g
        else
          let v = { v with gtge = PSet.add u.canon v.gtge } in
          change_node g v
    with
    | CycleDetected as e -> raise e
    | e ->
      (* Unlikely event: fatal error or signal *)
      let () = cleanup_marks g in
      raise e

  let add_node ?(rank=0) ?(ltle=PMap.empty) ?(gtge=PSet.empty) v g =
    let node = {
      canon = v;
      ltle = PMap.empty;
      gtge = PSet.empty;
      rank;
      klvl = 0;
      ilvl = g.index;
      status = NoMark;
    }
    in
    let entries = PMap.add v (Canonical node) g.entries in
    { entries; index = g.index - 1; n_nodes = g.n_nodes + 1; n_edges = g.n_edges; table = g.table }, node

  let add ?(rank=0) v g =
    if Index.mem v g.table then raise AlreadyDeclared
    else
      let () = assert (g.index > min_int) in
      let v, table = Index.fresh v g.table in
      fst (add_node ~rank v { g with table })

  exception Undeclared of Point.t
  let check_declared g us =
    let check l = if not (Index.mem (l, 0) g.table) then raise (Undeclared l) in
    Point.Set.iter check us

  exception Found_explanation of (constraint_type * Point.t) list

  let repr_expl g w idx =
    let can, weight = repr g ~w idx in
    let expl =
      if can.canon == idx then []
      else
        let p, w = Index.repr can.canon g.table in
        [(Eq (w-weight), p)]
    in
    can, weight, expl

  let get_explanation u v vn g =
    let v, weightv, explv = repr_expl g vn (Index.find v g.table) in
    let visited_strict = ref PMap.empty in
    let rec traverse weight u =
      if u == v then
        (Feedback.msg_debug Pp.(str "found: " ++ pr_can_weight g (u, 0) ++ str " weight is" ++ pr_incr weight);
        if weight > 0 then Some [] else None)
      else if topo_compare u v = 1 then None
      else
        let visited =
          (* Did we already visit this node through a path of larger weight? *)
          try (PMap.find u.canon !visited_strict >= weight)
          with Not_found -> false
        in
        if visited then None
        else begin
          visited_strict := PMap.add u.canon weight !visited_strict;
          try
            PMap.iter (fun u' weightu' ->
                Feedback.msg_debug Pp.(str "traversing: " ++ pr_repr_weight g (u', 0) ++ str "->" ++ pr_incr weightu' ++ str " weight is " ++ pr_incr weight);
                let canu', weightu', explu' = repr_expl g (weight - weightu') u' in
                match traverse weightu' canu' with
                | None -> ()
                | Some exp ->
                  let pu', wu' = Index.repr canu'.canon g.table in
                  let typ = Le (wu' + weightu') in
                  let expl = (typ, pu') in
                  let expleq = List.append explu' (expl :: exp) in
                  raise (Found_explanation expleq))
              u.ltle;
            None
          with Found_explanation exp -> Some exp
        end
    in
    let u, weightu, explu = repr_expl g 0 (Index.find u g.table) in
    let make_expl exp =
      List.append explu (List.append exp explv)
    in
    if u == v then
      let p, w = Index.repr v.canon g.table in
      make_expl [Eq (w + weightu - weightv), p]
    else match traverse (weightu - weightv) u with Some exp -> make_expl exp | None -> assert false

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
          if try let w' = PMap.find v.canon u.ltle in
              w' >= weight
            with Not_found -> false
          then raise (Found to_revert)
          else
            begin
              let next_todo =
                PMap.fold (fun u weightu next_todo ->
                    let u, weightu = repr_weight g u weightu in
                    let weight = weight - weightu in
                    if u == v && weight >= 0 then raise (Found to_revert)
                    else if topo_compare u v = 1 then next_todo
                    else (u, weight)::next_todo)
                  u.ltle next_todo
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
    let arcu, weightu = repr_node g ~w u and arcv, weightv = repr_node g v in
    arcu == arcv && weightu == weightv

  let check_smaller g weight u v =
    let u, weightu = repr_node g u in
    let v, weightv = repr_node g v in
    search_path (weight + weightu - weightv) u v g

  let check_leq g u n v = check_smaller g n u v

  let fresh_alias g p w =
    let idx, table = Index.fresh_alias p w g.table in
    { g with table }, idx

  let make_successor g u w =
    Feedback.msg_debug Pp.(str"Making successor of : " ++ pr_can_weight g (u, 0) ++ str " of weight " ++ pr_incr w);
    let p, w' = Index.repr u.canon g.table in
    let g, u' = fresh_alias g p (w + w') in
    let ltle = PMap.add u' w u.ltle in (* u + w <= u' *)
    let g = change_node g { u with ltle } in
    let g, canu' = add_node u' g in
    Feedback.msg_debug Pp.(str"Inserted edge : " ++ pr_can_weight g (u, 0) ++ str" <= " ++
      pr_can_weight g (canu', 0) ++ pr_incr (w));
    (* let g = enter_equiv g u.canon (-w) u' in *)
    let gtge = PSet.add u.canon canu'.gtge in
    let g = change_node g { canu' with gtge } in
    { g with n_nodes = g.n_nodes + 1; n_edges = g.n_edges + 1 }, canu'

  (* insert_edge u w v adds an edge u + w <= v *)
  let insert_edge w u v g =
    Feedback.msg_debug (let vn = v in
    Pp.(str"Inserting edge of weight " ++ int w ++ str " between " ++
    pr_can_weight g (u, 0) ++ str" and " ++ pr_can_weight g (vn, 0)));
    if w >= 0 then insert_edge w u v g
    else
      (* If we want to insert an arc of negative weight, we rather make an alias
        u' of u - w and replace u with u' + w everywhere. Then we can add u' <= v.
      *)
      (let vn = v in Feedback.msg_debug Pp.(str"Building alias for " ++ pr_can_weight g (vn, -w));
      let g, canv' = make_successor g v (-w) in
      let src, src_weight = repr_node g (Point.source, 0) in
      Feedback.msg_debug Pp.(str"Source is represented by " ++ pr_can_weight g (src, src_weight));
      let () = assert (src_weight = 0) in
      Feedback.msg_debug Pp.(str"Alias represents " ++ pr_can_weight g (canv', 0));
      let g = insert_edge 0 src canv' g in
      insert_edge 0 u canv' g)

  (* enforce_eq g u n v will force u + n = v if possible, will fail otherwise *)

  let enforce_eq u n v g =
    let ucan, weightu = repr_node g u in
    let weightu = n + weightu in
    let vcan, weightv = repr_node g v in
    let weight = weightu - weightv in
    if ucan == vcan then
      if Int.equal weight 0 then g
      else Point.error_inconsistency (Eq n) u v None
    else if topo_compare ucan vcan = 1 then
      let g = insert_edge (-weight) vcan ucan g in  (* Cannot fail *)
      try insert_edge weight ucan vcan g
      with CycleDetected ->
        Point.error_inconsistency (Eq (- n)) v u (get_explanation v u (n) g)
    else
      let g = insert_edge weight ucan vcan g in  (* Cannot fail *)
      try insert_edge (-weight) vcan ucan g
      with CycleDetected ->
        Point.error_inconsistency (Eq (-n)) v u (get_explanation v u (-n) g)

  (* enforce_leq g u v will force u<=v if possible, will fail otherwise *)
  let enforce_leq u n v g =
    let ucan, weightu = repr_node g u in
    let vcan, weightv = repr_node g v in
    try insert_edge (n + weightu - weightv) ucan vcan g
    with CycleDetected ->
      Point.error_inconsistency (Le n) u v (get_explanation u v (-n) g)

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
      | Canonical {canon=u; ltle; _} ->
        PMap.fold (fun v weight acc ->
            let u, uw = Index.repr u g.table in
            let v, vw = Index.repr v g.table in
            let typ = Le (uw - vw + weight) in
            Constraint.add (u,typ,v) acc) ltle acc
      | Equiv (v, n) ->
        (* u = v + n *)
        let u, uw = Index.repr u g.table in
        let v, vw = Index.repr v g.table in
        if uw == vw + n then UF.union u v uf; acc
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
    let kept = Point.Set.fold (fun u accu -> PSet.add (Index.find u g.table) accu) kept PSet.empty in
    let rmap, csts = PSet.fold (fun u (rmap,csts) ->
        let arcu, weightu = repr g u in
        if PSet.mem arcu.canon kept then
          let csts = if Index.equal u arcu.canon then csts
            else add_cst u (Eq (-weightu)) arcu.canon csts
          in
          PMap.add arcu.canon (0, arcu.canon) rmap, csts
        else
          match PMap.find arcu.canon rmap with
          | (weightv, v) -> rmap, add_cst u (Eq (- (weightv + weightu))) v csts
          | exception Not_found -> PMap.add arcu.canon (weightu, u) rmap, csts)
        kept (PMap.empty,Constraint.empty)
    in
    let rec add_from u csts todo = match todo with
      | [] -> csts
      | (v,weight)::todo ->
        let v, weightv = repr_weight g v weight in
        (match PMap.find v.canon rmap with
         | weightv', v ->
           let d = Le (weightv + weightv') in
           let csts = add_cst u d v csts in
           add_from u csts todo
         | exception Not_found ->
           (* v is not equal to any kept point *)
           let todo = PMap.fold (fun v' weight' todo ->
               (v', weight + weight') :: todo)
               v.ltle todo
           in
           add_from u csts todo)
    in
    PSet.fold (fun u csts ->
        let ru = repr g u in
        PMap.fold (fun v weight csts -> add_from u csts [v,weight])
          (repr_ltle ru) csts)
      kept csts

  let domain g =
    let fold u _ accu = Point.Set.add (fst (Index.repr u g.table)) accu in
    PMap.fold fold g.entries Point.Set.empty

  let choose p g u =
    let exception Found of Point.t in
    let ru, weightu = repr_node g u in
    let ru = ru.canon in
    let ruv, ruvw = Index.repr ru g.table in
    if p ruv then Some ruv
    else
      try PMap.iter (fun v -> function
          | Canonical _ -> () (* we already tried [p ru] *)
          | Equiv (v', n) ->
            let rv, weightv = repr_weight g v' n in
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
        let fold v weight accu =
          let v, vw = Index.repr v g.table in
          Point.IMap.add (v, vw) weight accu in
        let ltle = PMap.fold fold n.ltle Point.IMap.empty in
        let fold u accu = Point.Set.add (fst (Index.repr u g.table)) accu in
        let gtge = PSet.fold fold n.gtge Point.Set.empty in
        Node (ltle, gtge)
      | Equiv (v, n) ->
        let v, vw = Index.repr v g.table in
        Alias (v, vw + n)
      in
      Point.IMap.add (pu, uw) n accu
    in
    PMap.fold fold g.entries Point.IMap.empty

end
