(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module W :
sig
  type t
  val zero : t
  val minus_one : t
  val of_int : int -> t
  val to_int : t -> int
  val inf : t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val (~-) : t -> t
  val (<) : t -> t -> bool
  val min : t -> t -> t
  val (<=) : t -> t -> bool
  val (=) : t -> t -> bool
end =
struct
  type t = int

  let check_overflow r =
  (* These bounds should be enough for any concrete applications, and
     make it easy to detect overflows. *)
    if r > (1 lsl 30) - 1 || r < - (1 lsl 30) then
      CErrors.anomaly ~label:"AcyclicGraph.W.add"
        Pp.(str"Overflow in constraint weight");
    r

  let zero = 0 and minus_one = -1 and inf = max_int
  let of_int = check_overflow
  let to_int x = x
  let (+) x y =
    if x = inf || y = inf then inf
    else check_overflow (x+y)
  let (-) x y =
    assert (y < inf);
    if x = inf then inf else check_overflow (x-y)
  let (~-) x = check_overflow (-x)
  let (<) (x : int) (y : int) = x < y
  let min (x : int) (y : int) = min x y
  let (<=) (x : int) (y : int) = x <= y
  let (=) = Int.equal
end

type constraint_weight = W.t
let weight_le = W.zero
let weight_lt = W.minus_one
let weight_of_int = W.of_int

type constraint_type = Eq | Le

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  module Constraints : CSet.S with type elt = (t * constraint_type * constraint_weight * t)

  val equal : t -> t -> bool
  val compare : t -> t -> int

  type explanation = (constraint_type * W.t * t) list
  val error_inconsistency :
    t -> constraint_type -> W.t -> t -> explanation lazy_t option -> 'a

  val pr : t -> Pp.t
end

module Make (Point:Point) = struct
  (* Constraints directly required by the type system are of the form
     x < y and x <= y (i.e., a = -1 and a = 0), but user anotations
     and universe polymorphism sometimes generate constraints of the
     form x - y = a, so that finally we support all the constraints of
     the form x - y <= a.

     This file contains a library which detects the first
     inconsistency among these constraints. Formally, this amounts to
     detecting a negative cycle in a weigthed directed graph. A simple
     approach would consist in maintaining the matrix of all shortest
     paths, and warn when a diagonal element becomes negative.

     However, with this algorithm, adding a single constraint would
     take quadratic time, which is way too slow. We use two important
     improvements to this approach:

       - We expect the universe graph to contain mainly constraints of
         the form x - y <= 0 and x - y < 0, so that we expect strongly
         connected components to be small. Hence, we maintain strongly
         connected components and check for negative cycles using the
         matrix of all-shortests paths only in these strongly connected
         components. Strongly connected components maintainance is a
         well-known problem for which there exists (subtle) off-the-shelf
         algorithms. We use the algorithm described in the paper:

         Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E.
         (2015). A new approach to incremental cycle detection and
         related problems. ACM Transactions on Algorithms (TALG),
         12(2), 1-22.

       - We also expect constraints of the form x + y = a to appear
         relatively often (in particular with a = 0). They correspond
         to a cycle of weight 0 in the graph. In the algorithm, we use
         a union-find data structure to maintain the partition of
         zero-cycles, and keep in the main data structure only one
         representative of each of these classes.
   *)

  (* Points are re-indexed using integers, which are easier to compare
     and to use as keys in data structures. *)
  module Key :
  sig
    type t
    val equal : t -> t -> bool
    module Set : CSig.SetS with type elt = t
    module Map : CMap.ExtS with type key = t and module Set := Set
    module Hashtbl : Hashtbl.S with type key = t
    type table
    val empty : table
    val fresh : Point.t -> table -> t * table
    val mem : Point.t -> table -> bool
    val of_point : Point.t -> table -> t
    val to_point : t -> table -> Point.t
  end =
  struct
    type t = int
    let equal = Int.equal
    module Set = Int.Set
    module Map = Int.Map
    module Hashtbl = Hashtbl.Make(Int)

    type table = {
      tab_len : int;
      tab_fwd : Point.t Int.Map.t;
      tab_bwd : int Point.Map.t
    }

    let empty = {
      tab_len = 0;
      tab_fwd = Int.Map.empty;
      tab_bwd = Point.Map.empty;
    }
    let mem x t = Point.Map.mem x t.tab_bwd
    let of_point x t =
      try Point.Map.find x t.tab_bwd
      with Not_found ->
        CErrors.anomaly ~label:"Univ.Key.of_point"
          Pp.(str"Universe " ++ Point.pr x ++ str" undefined.")
    let to_point n t = Int.Map.find n t.tab_fwd

    let fresh x t =
      let () = assert (not @@ mem x t) in
      let n = t.tab_len in
      n, {
        tab_len = n + 1;
        tab_fwd = Int.Map.add n x t.tab_fwd;
        tab_bwd = Point.Map.add x n t.tab_bwd;
      }
  end

  module KMap = Key.Map
  module KSet = Key.Set
  module KHashtbl = Key.Hashtbl
  module Constraints = Point.Constraints

  exception Inconsistent

  (* A matrix of all-shortest paths (in a strongly connected
     component). *)
  module DistMat :
  sig
    type t
    val singleton : t
    val merge : t list -> t
    (* Adding a constraint also detect the potential new 0-cycle and keep only
       one representative for it in the matrix.
       - The representative is choosen with maximal rank.
       - If such a cycle is found, it returns the index of the kept node, the
         distance of each node in the cycle, and a Boolean indicating wether
         the maximal rank is a tie.  *)
    val add_constraint :
      ?rank:(int -> int) ->
      int -> W.t -> int -> t ->
      t * (W.t option array * int * bool) option
    val dist : int -> int -> t -> W.t
    val size : t -> int
    val check_invariants : allow_inf:bool -> t -> unit
  end =
  struct
    type t = W.t array array

    let singleton = [|[|W.zero|]|]

    let merge cl =
      let n = List.fold_left (fun n c -> n + Array.length c) 0 cl in
      let r = Array.make_matrix n n W.inf in
      let off = ref 0 in
      cl |> List.iter (fun c ->
          let nc = Array.length c in
          for i = 0 to nc - 1 do
            Array.blit c.(i) 0 r.(!off+i) !off nc
          done;
          off := !off + nc);
      assert (!off = n);
      r

    let add_constraint ?(rank : int -> int = (fun _ -> assert false)) i1 wi1i2 i2 c =
      if W.(c.(i1).(i2) <= wi1i2) then c, None
      else (* If i1 = i2, then w < 0 ... *)
        let wcycle = W.(c.(i2).(i1) + wi1i2) in
        if W.(wcycle < zero) then raise Inconsistent
        else (* ... so here we know than i1 <> i2 *)
          let di2 = c.(i2) in
          (* Using the new inserted edge, we recompute all the
             shortest paths. They are either a former shortest path,
             or the concatenation of a former shortest path, the new
             edge and a former shortest path. *)
          let c =
            c |> Array.map (fun di ->
                let wii2 = W.(di.(i1) + wi1i2) in
                if W.(di.(i2) <= wii2) then di
                else Array.map2 (fun dij di2j -> W.(min (wii2 + di2j) dij)) di di2)
          in
          if not W.(wcycle = zero) then c, None
          else
            (* We have created a cycle of weight 0. Let's collapse it. *)
            let n = Array.length c in
            let shifts = Array.make n None in
            let maxrk = ref (rank i1) and imax = ref i1 and tie = ref false in
            let n' = ref n in
            for i = 0 to n - 1 do
              if i <> i1 && W.(c.(i).(i1) + c.(i1).(i) = zero) then begin
                (* If [i] is part of the 0-cycle (and [i] is not [i1], which is
                   treated separately.) *)
                let rk = rank i in
                if rk <= !maxrk then begin
                  shifts.(i) <- Some W.zero;
                  if rk = !maxrk then tie := true
                end else (* rk > maxrk *) begin
                  shifts.(!imax) <- Some W.zero;
                  maxrk := rk; imax := i; tie := false
                end;
                decr n'
              end
            done;
            let r = Array.make !n' [||] in
            let ii = ref 0 in
            for i = 0 to n - 1 do
              if shifts.(i) = None then begin
                let d = Array.make !n' W.zero in
                let jj = ref 0 in
                for j = 0 to n - 1 do
                  if shifts.(j) = None then begin
                    d.(!jj) <- c.(i).(j);
                    incr jj
                  end
                done;
                assert (!jj = !n');
                r.(!ii) <- d;
                incr ii
              end else shifts.(i) <- Some c.(i).(!imax)
            done;
            assert (!ii = !n');
            r, Some (shifts, !imax, !tie)

    let dist i j c = c.(i).(j)

    let size = Array.length

    let check_invariants ~allow_inf c =
      let n = Array.length c in
      c |> Array.iter (fun d -> assert (Array.length d = n));
      for i = 0 to n - 1 do
        assert W.(c.(i).(i) = zero);
        for j = 0 to n - 1 do
          for k = 0 to n - 1 do
            assert W.(c.(i).(k) <= c.(i).(j) + c.(j).(k));
          done
        done
      done;
      for i = 0 to n - 1 do
        for j = 0 to n - 1 do
          assert (i = j || W.(c.(i).(j) + c.(j).(i) > zero))
        done
      done;
      if not allow_inf then
        for i = 0 to n - 1 do
          for j = 0 to n - 1 do
            assert W.(c.(i).(j) < W.inf)
          done
        done
  end

  (* Information stored for a strongly connected component.
     Comparison on this type is pointer equality. *)
  type scc =
    { nodes: Key.t array;
      dists: DistMat.t;
      fwd: W.t KMap.t array;
      bwd: KSet.t;
      (* [bwd] contains backward SCC neightbors only at the same level. *)
      klvl: int;
      ilvl: int }

  (* A Point.t is either
       - a (shifted) alias for another one (in a 0-cycle)
       - a node which belongs to a SCC but is not its head. It points *directly*
          to its SCC head.
       - the canonical head of an SCC.
     We consider the set of shift links as a union-find data structure.
     The head of a shift link sequence is either a [SccOf] or a [SccHead].
     It contains the rank (for the union-find rank optimization).
 *)
  type entry =
    | Shift of W.t * Key.t
    | SccOf of Key.t * int * int  (* first [int] is index in SCC, second [int] is rank *)
    | SccHead of scc * int  (* [int] is rank *)

  type t =
    { entries : entry KMap.t;
      (* Next available index for topological ordering in each k-level. *)
      index : int;
      (* Table for translating between [Key.t] (internal) and [Point.t] (external). *)
      table : Key.table }

  let key u = u.nodes.(0)

  (* Change data associated with a SCC head.
     [key n] should already been inserted as a SCC head or with SccOf. *)
  let change_node g n =
    { g with entries = g.entries |> KMap.modify (key n) (fun _  -> function
                           | SccHead (_, r) -> SccHead (n, r)
                           | SccOf (_, _, r) -> SccHead (n, r)
                           | _ -> assert false) }

  let enter_sccof g u v i =
    { g with entries = g.entries |> KMap.modify u (fun _ -> function
                           | SccHead (_, r) -> SccOf (v, i, r)
                           | SccOf (_, _, r) -> SccOf (v, i, r)
                           | Shift _ -> assert false) }

  let incr_rank g u =
    { g with entries = g.entries |> KMap.modify u (fun _ a ->
                           match a with
                           | SccHead (v, r) -> SccHead (v, r+1)
                           | SccOf (v, i, r) -> SccOf (v, i, r+1)
                           | Shift _ -> assert false) }

  let rank g u =
    match KMap.find u g.entries with
    | SccOf (_, _, r) | SccHead (_, r) -> r
    | _ -> assert false

  let get_scc g u =
    match KMap.find u g.entries with
    | SccHead (v, _) -> v | _ -> assert false

  (* canonical SCC head representative :
     we follow the Shift/SccOf links *)
  let rec repr_scc g u =
    match KMap.find u g.entries with
    | Shift (_, v) -> repr_scc g v
    | SccHead (u, _) -> u, 0
    | SccOf (v, i, _) -> get_scc g v, i

  (* canonical shifted representative :
     we follow only Shift links *)
  let repr_shift g u =
    let rec loop w u =
      match KMap.find u g.entries with
      | Shift (w', v) -> loop W.(w + w') v
      | _ -> w, u
    in
    loop W.zero u

  let find_in_nodes nodes u =
    let rec loop i =
      if i = Array.length nodes then raise Not_found
      else if Key.equal nodes.(i) u then i else loop (i+1)
    in
    loop 0

  let repr g u =
    let w, u = repr_shift g u in
    let uc, i = repr_scc g u in
    w, u, uc, i

  (* Reindexes the given SCCs, using the next available indices. *)
  let rec use_indices g = function
    | [] -> g
    | u :: ul ->
      let g = change_node g { (get_scc g u) with ilvl = g.index } in
      assert (g.index > min_int);
      use_indices { g with index = g.index - 1 } ul

  (* Returns 1 if u is higher than v in topological order.
             -1        lower
             0 if u = v *)
  let topo_compare u v =
    if u.klvl > v.klvl then 1
    else if u.klvl < v.klvl then -1
    else if u.ilvl > v.ilvl then 1
    else if u.ilvl < v.ilvl then -1
    else (assert (u==v); 0)

  module TMap = Map.Make(struct type t = scc let compare = topo_compare end)

  (* Checks most of the invariants of the graph. For debugging purposes. *)
  let check_invariants ~required_canonical g =
    let required_canonical u = required_canonical (Key.to_point u g.table) in
    g.entries |> KMap.iter (fun l -> function
        | SccHead (u, _) ->
          u.fwd |> Array.iter (fun fwd -> fwd |> KMap.iter (fun v _w ->
              let v, _ = repr_scc g v in
              assert (topo_compare u v = -1);
              if u.klvl = v.klvl then
                assert (KSet.mem (key u) v.bwd ||
                        KSet.exists (fun l -> u == fst (repr_scc g l)) v.bwd)));
          u.bwd |> KSet.iter (fun v ->
              let v, _ = repr_scc g v in
              assert (v.klvl = u.klvl);
              assert (Array.exists (KMap.mem (key u)) v.fwd ||
                      Array.exists (KMap.exists (fun l _ -> u == fst (repr_scc g l))) v.fwd));
          assert (Key.equal l (key u));
          assert (u.ilvl < 0 && u.ilvl > g.index);
          DistMat.check_invariants ~allow_inf:false u.dists;
          u.nodes |> Array.iteri (fun iv v ->
              assert (Key.equal (snd (repr_shift g v)) v);
              assert (fst (repr_scc g v) == u);
              u.nodes |> Array.iteri (fun iv' v' ->
                  assert (not (Key.equal v v') || iv = iv')));
          assert (Array.length u.nodes = Array.length u.fwd);
          assert (DistMat.size u.dists = Array.length u.fwd)
        | SccOf (v, i, _) ->
           assert (Key.equal (get_scc g v).nodes.(i) l)
        | Shift _ -> assert (not (required_canonical l)))

  let clean_fwd g fwd =
    let chg = ref false in
    let fwd' = fwd |> Array.map (fun m ->
          KMap.fold (fun u w acc ->
              let w_shift, uu = repr_shift g u in
              if Key.equal uu u then acc
              else begin
                let acc = KMap.remove u acc in
                let w = W.(w + w_shift) in
                chg := true;
                acc |> KMap.update uu (function
                    | None -> Some w
                    | Some w_uu when W.(w < w_uu) -> Some w
                    | x -> x)
              end)
            m m)
    in
    if !chg then fwd' else fwd

  let clean_bwd g bwd =
    let chg = ref false in
    let bwd' =
      KSet.fold (fun u acc ->
          let uu = key (fst (repr_scc g u)) in
          if Key.equal uu u then acc
          else begin chg := true; KSet.add uu (KSet.remove u acc) end)
        bwd bwd
    in
    if !chg then bwd' else bwd

  (* Add an edge of weight [w] between nodes numbered [ui] and [vi] of
     SCC [c], in graph [g].
     If this creates 0-cycles, then create shift links in the graph. *)
  let add_internal_edge ui w vi c g =
    let rank i = rank g c.nodes.(i) in
    match DistMat.add_constraint ui w vi c.dists ~rank with
    | dists, None -> change_node g { c with dists }
    | dists, Some (shifts, iroot, tie) ->
      let n = DistMat.size dists in
      let root = c.nodes.(iroot) in
      let fwdroot = ref c.fwd.(iroot) in
      let nodes = Array.make n root and fwd = Array.make n KMap.empty in
      let ii = ref 0 in
      let g = ref g in
      for i = 0 to Array.length shifts - 1 do
        match shifts.(i) with
        | None ->
          nodes.(!ii) <- c.nodes.(i); fwd.(!ii) <- c.fwd.(i);
          (* If the index of the node in [nodes] changes, then we need to update the corresponding
             information in [g.entries]. *)
          if !ii <> i && !ii <> 0 then g := enter_sccof !g nodes.(!ii) nodes.(0) !ii;
          incr ii
        | Some wi ->
          fwdroot := KMap.merge (fun _ wold w ->
                         match wold, w with
                         | _, None -> wold
                         | None, Some w -> Some W.(w - wi)
                         | Some wold, Some w -> Some W.(min wold (w - wi)))
                       !fwdroot c.fwd.(i);
          g := { !g with
                 entries = KMap.set c.nodes.(i) (Shift (wi, root)) !g.entries }
      done;
      assert (!ii = n);
      fwd.(find_in_nodes nodes root) <- !fwdroot;
      let g = change_node !g { c with nodes; dists; fwd } in
      if tie then incr_rank g root else g

  let add_external_edge uc ui w vc vi g =
    assert (topo_compare uc vc = -1);
    let fwdui = uc.fwd.(ui) |> KMap.update vc.nodes.(vi) (function
      | None -> Some w
      | Some w' -> Some (W.min w w'))
    in
    if fwdui == uc.fwd.(ui) then g
    else begin
      let fwd = Array.copy uc.fwd in fwd.(ui) <- fwdui;
      let g = change_node g { uc with fwd } in
      if uc.klvl <> vc.klvl then g
      else change_node g { vc with bwd = KSet.add (key uc) vc.bwd }
    end

  (* Implementation of the algorithm described in § 4.1 of the following paper:

         Bender, M. A., Fineman, J. T., Gilbert, S., & Tarjan, R. E.
         (2015). A new approach to incremental cycle detection and
         related problems. ACM Transactions on Algorithms (TALG),
         12(2), 1-22.

     The "STEP X" comments contained in this file refers to the
     corresponding step numbers of the algorithm described in Section
     4.1 of this paper.

     In addition, we maintain a topological ordering on edges by storing
     indices on nodes, as described at the end of § 2 of the same paper. *)

  (* [u] must be SCC head.
     The backward traversal is limited to the current level.
     [count] limits the number of traversed edges. If the count is reached,
     the traversal is aborted. *)
  let backward_traverse count g u =
    let visited = KHashtbl.create 32 in
    let g = ref g and count = ref count in
    let exception AbortBackward in
    let rec go u =              (* [u] is SCC head. *)
      decr count;
      if !count < 0 then raise AbortBackward;
      if not (KHashtbl.mem visited u) then begin
        KHashtbl.replace visited u ();
        let c = get_scc !g u in
        let bwd = clean_bwd !g c.bwd in
        if bwd != c.bwd then g := change_node !g { c with bwd };
        KSet.iter go bwd
      end
    in
    try go u; !g, true with AbortBackward -> !g, false

  (* The forward traversal is limited to nodes whose level is below [klvl],
     and moves traversed nodes to that level. It also updates [bwd] fields
     accordingly.
     [v] the start of the traversal. *)
  let forward_traverse klvl g v =
    let g = ref g in
    let f_traversed = ref [] in
    let rec go from v =         (* [from] is SCC head. *)
      let c, _ = repr_scc !g v in
      if c.klvl < klvl then begin
        let fwd = clean_fwd !g c.fwd in
        let bwd = match from with None -> KSet.empty | Some from -> KSet.singleton from in
        g := change_node !g { c with klvl; fwd; bwd };
        let v = key c and from = Some v in
        Array.iter (KMap.iter (fun v' _  -> go from v')) fwd;
        f_traversed := v :: !f_traversed
      end else if c.klvl = klvl then match from with None -> () | Some from ->
        g := change_node !g { c with bwd = KSet.add from c.bwd }
    in
    go None v;
    !f_traversed, !g

  (* [u] and [v] need to be SCC heads.

     [classify] needs to be called when [v] and [u] are at the same level.
     [classify] returns a triple [f_to_reindex, to_merge, b_to_reindex] of
     lists:
        - If not empty, [to_merge] is the lists of SCC that need to be
          merged when adding an edge from [u] to [v] (i.e., they are both
          accessible from [v] and coaccessible from [u]). In particular, if
          [to_merge] is not empty, it includes [u].
        - [f_to_reindex] and [b_to_reindex] are lists of SCC that needs to be
          reindexed in the current level because of the edge insertion. The
          lists are returned in the order of reindexing (this is the reverse
          final index order, since indices are given downwards).
          [f_to_reindex] needs to be reindexed first, and then [b_to_reindex].
          If there is a merged SCC, it needs to be placed inbetween. Formally:
             + [f_to_reindex] is the reversed subset of [f_traversed] of SCCs
               not in [to_merge].
             + [b_to_reindex] is the set of coaccessible SCCs from [u], which
               are not in [to_merge]

     The algorithm proceeds by traversing backward the current level, starting
     from [u]. Hence, we will only traverse nodes that we traversed in the
     backward traversal or that we leveled up in the forward traversal. This has
     two fortunate consequences for us:
        - The time complexity of [classify] (which is not clearly discussed
          in the paper) is amortized by these two traversals.
        - The [bwd] fields we use are aleready clean, either because cleaned
          during the backward traversal or created cleanly during the forward
          traversal. *)
  let classify g u v f_traversed =
    let tab = KHashtbl.create 32 in
    let b_to_reindex = ref [] in
    let to_merge = ref [] in
    let rec go x =              (* [x] is SCC head. *)
      try KHashtbl.find tab x with Not_found ->
        let m =
          (* We know for sure that [(get_scc g x).bwd] is clean because it has
             either been already cleaned by backward traversal, or it has been
             built cleanly by forward traversal. *)
          KSet.fold (fun y m -> go y || m) (get_scc g x).bwd false
          || Key.equal x v
        in
        KHashtbl.replace tab x m;
        if m then to_merge := x :: !to_merge
        else b_to_reindex := x :: !b_to_reindex;
        m
    in
    ignore (go u);
    f_traversed |> CList.rev_filter (fun x -> not (KHashtbl.mem tab x)),
    !to_merge, !b_to_reindex

  (* Merge the SCCs in [to_merge] into one new SCC, updating [fwd] and [bwd]
     links.
     Also add [SccOf] links in the graph for nodes which are no longer heads.
     This assumes that [bwd] fields are already cleaned (see comment above
     [classify] so as to why this is true).
     The new SCC is not quite yet strongly connected, because the new edge is
     not added at this point. As a result, the constraints we add to the new SCC
     cannot create new shift links, so we don't need to take care about this
     here. *)
  let do_merge g klvl to_merge =
    assert (match to_merge with _::_::_ -> true | _ -> false);
    let to_merge = to_merge |> List.map (get_scc g) in
    let dists = ref (DistMat.merge (to_merge |> List.map (fun u -> u.dists))) in
    let fwd = Array.concat (to_merge |> List.map (fun u -> clean_fwd g u.fwd)) in
    let nodes = Array.concat (to_merge |> List.map (fun u -> u.nodes)) in
    let n = Array.length nodes in
    for i = 0 to n - 1 do
      fwd.(i) <- fwd.(i) |> KMap.filter (fun u w ->
        match find_in_nodes nodes u with
        | exception Not_found -> true
        | j ->
          let d, shifts = DistMat.add_constraint i w j !dists in
          assert (shifts = None);
          dists := d;
          false)
    done;
    let bwd = List.fold_left (fun acc n -> KSet.union acc n.bwd) KSet.empty to_merge in
    let bwd = List.fold_left (fun acc n -> KSet.remove (key n) acc) bwd to_merge in
    let g = change_node g { nodes; dists = !dists; fwd; bwd; klvl; ilvl = 0 (* dummy *) } in
    let g = ref (use_indices g [nodes.(0)]) in
    for i = 1 to Array.length nodes - 1 do
      g := enter_sccof !g nodes.(i) nodes.(0) i
    done;
    !g

  (* [u] and [v] must be SCC heads.
     [v] should be (strictly) lower than [u] in topological order.
     The goal of this function is to reverse this order, while preserving all
     the invariants of the graph.
     If [u] is accessible from [v], then this function also merges nodes which
     are accessible from [v] and coaccessible from [u]. In this case, we are
     creating a new "SCC" for these nodes, which is not yet an SCC since the
     edge from [u] to [v] is missing. This is the only invariant possibly
     broken by this function.

     How is this reordering performed? The idea, is to both move [u] down and
     [v] up in the topological order. When we do this, we will need to also
     move some nodes coaccessible from [u] and some accesible from [v] to
     preserve the topological ordering property. More precisely:
       - We try to move [u] and all of its coaccesible nodes of the same level
         at the bottom of that level. But we only do this if this is not too
         costly: at level [k], we can only afford moving [k+1] edges in this
         stage. Determining whether or not this is too costly is done through
         the *backward traversal*.
       - We move [v] up by changing its level to that of [u] (if the
         backward traversal succeeded) or to one level higher than that
         of [u] (otherwise). Provided there is no path from [v] to [u], we know
         for sure that in both cases [v] will be higher than [u] in the
         topological order. This is because either the backward traversal
         succeeded, and [v] is cleverly inserted higher than [u] in its level,
         or because the backward traversal failed and [v] will have a higher
         level than [u]. Of course, we also need to update the levels of nodes
         accessible from [v] to preserve the invariants. This is what we call
         the *forward traversal*.
       - In order to detect if we just created a cycle (which we need to squash
         in a new SCC) and determine which nodes belong to this cycle, we see
         that a necessary condition is that [u] and [v] belong to the same
         level. This is either because the backward traversal succeeded and we
         made [u] belong to the level of [v], or because it failed and [u] has
         been reached by the forward traversal. Hence we do a second backward
         search from [u], limited to the current level. This is what [classify]
         does.
     In practice, we delay changing the indices of nodes (during the forward
     and bacward traversal), because we need to insert nodes traversed during
     the backward traversal just above nodes traversed during the backward
     traversal.

     Interestingly, the only information that we get from the backward traversal
     is only a Boolean: whether the subgraph of coaccesible nodes from [u] at
     its level is large. The topologically sorted list of nodes coaccessible
     from [u] at its level is computed by [classify]. *)
  let reorder g u v =
    (* We take care to not use a variable for [get_scc g u] and [get_scc g v] of
       [u] and [v] because they can be modified by the traversals. *)

    (* STEP 2: backward traversal in the k-level of u. *)
    let klvl = (get_scc g u).klvl in
    let g, backward_success = backward_traverse klvl g u in
    let klvl = klvl + if backward_success then 0 else 1 in

    (* STEP 3: forward traversal. Contrary to what is described in
        the paper, we do not test whether klvl = u.klvl nor we assign
        klvl to v.klvl. Indeed, the first call to forward_traverse
        will do all that. *)
    let f_traversed, g = forward_traverse klvl g v in

    (* STEP 4: merge nodes if needed. *)
    if (get_scc g u).klvl = klvl then begin
      let f_to_reindex, to_merge, b_to_reindex = classify g u v f_traversed in
      let g = use_indices g f_to_reindex in
      let g = if to_merge = [] then g else do_merge g klvl to_merge in
      use_indices g b_to_reindex
    end else use_indices g (List.rev f_traversed)

  (* Does NOT assume that [u != v]. *)
  let insert_edge u w v g =
    (* STEP 1: do we need to reorder nodes ? *)
    let uc, _ = repr_scc g u and vc, _ = repr_scc g v in
    let g = if topo_compare uc vc <= 0 then g else reorder g (key uc) (key vc) in

    (* STEP 5: insert the new edge in the graph. *)
    (* We redo these repr lookups because nodes can be merged during the
       call to [reorder]. *)
    let uw, _, uc, ui = repr g u in
    let vw, _, vc, vi = repr g v in
    let w = W.(w + vw - uw) in
    if uc == vc then add_internal_edge ui w vi uc g
    else add_external_edge uc ui w vc vi g

  exception AlreadyDeclared
  let add ?(rank=0) v g =
    if Key.mem v g.table then raise AlreadyDeclared
    else
      let () = assert (g.index > min_int) in
      let v, table = Key.fresh v g.table in
      let node = {
        nodes = [| v |]; dists = DistMat.singleton;
        fwd = [| KMap.empty |]; bwd = KSet.empty;
        klvl = 0; ilvl = g.index }
      in
      { entries = KMap.add v (SccHead (node, rank)) g.entries;
        index = g.index - 1;
        table }

  let add_shift u w v g =
    if Key.mem u g.table then raise AlreadyDeclared
    else
      let wv, v = repr_shift g (Key.of_point v g.table) in
      let u, table = Key.fresh u g.table in
      { g with entries = KMap.add u (Shift (W.(w + wv), v)) g.entries;
               table }

  exception Undeclared of Point.t
  let check_declared g us =
    us |>
    Point.Set.iter (fun l -> if not (Key.mem l g.table) then raise (Undeclared l))

  let traverse_explain w u vc vi g =
    let visited_weight = KHashtbl.create 32 in
    let rec go w u =
      let uw, u', uc, ui = repr g u in
      if not (Key.equal u u') then
        match go W.(w - uw) u' with
        | Some exp -> Some ((Eq, uw, Key.to_point u' g.table)::exp)
        | None -> None
      else (* u' = u *) match topo_compare uc vc with
      | 0 when W.(DistMat.dist ui vi uc.dists < w) ->
        if ui = vi then Some []
        else Some [(Le, DistMat.dist ui vi uc.dists, Key.to_point vc.nodes.(vi) g.table)]
      | 0 | 1 -> None
      | _ (* -1 *) ->
        let visited =
          match KHashtbl.find_opt visited_weight u with
          | None -> false | Some w' -> W.(w <= w')
        in
        if visited then None
        else begin
          KHashtbl.replace visited_weight u w;
          let exception Found_explanation of Point.explanation in
          try
            uc.fwd |> Array.iteri (fun i fwd ->
              let w = W.(w - DistMat.dist ui i uc.dists) in
              fwd |> KMap.iter (fun u' w' ->
                match go (W.(w - w')) u' with
                | None -> ()
                | Some exp ->
                   let exp = (Le, w', Key.to_point u' g.table) :: exp in
                   let exp =
                     if i = ui then exp
                     else (Le, DistMat.dist ui i uc.dists,
                           Key.to_point uc.nodes.(i) g.table) :: exp
                   in
                   raise (Found_explanation exp)));
            None
          with Found_explanation exp -> Some exp
        end
    in
    go w u

  let get_explanation u w v g =
    let v0 = v in
    let vw, v, vc, vi = repr g v in
    match traverse_explain W.(vw + w) u vc vi g with
    | Some exp ->
      if Key.equal v0 v then exp
      else (Eq, W.(-vw), Key.to_point v g.table)::exp
    | None ->
      CErrors.anomaly ~label:"AcyclicGraph.get_explanation"
        Pp.(str"Cannot find negative cycle.")

  let get_explanation u w v g =
    Some (lazy (get_explanation
                  (Key.of_point u g.table) w (Key.of_point v g.table) g))

  let explained_error u ty w v g =
    Point.error_inconsistency u ty w v (get_explanation v W.(-w) u g)

  (* To compare two nodes, we simply do a forward search.
     We implement two improvements:
     - we ignore nodes that are higher than the destination;
     - we do a BFS rather than a DFS because we expect to have a short
         path (typically, the shortest path has length 1)
     TODO : we could try to explore in topological order, to make sure that we
            explore a node only once. The downside is that we will less quickly
            find non-trivial paths of short length.
  *)
  let search_path u w0 v g =
    let wu, _, u, ui = repr g u in
    let wv, _, v, vi = repr g v in
    if u == v then W.(wu + DistMat.dist ui vi u.dists - wv <= w0)
    else begin
      let best_w = KHashtbl.create 32 in
      let get_best_w u ui =
        try KHashtbl.find best_w u.nodes.(ui) with Not_found -> W.inf
      in
      let todo = Queue.create () in
      Queue.push (u, ui, W.(wu - wv)) todo;
      let exception Found in
      try while true do
        let u, ui, w = Queue.pop todo in
        if W.(w < get_best_w u ui) then begin
          begin match KMap.find_opt v.nodes.(vi) u.fwd.(ui) with
          | Some w' when W.(w + w' <= w0) -> raise Found
          | _ -> ()
          end;
          for i = 0 to Array.length u.nodes - 1 do
            let w = W.(w + DistMat.dist ui i u.dists) in
            if W.(w < get_best_w u i) then begin
              KHashtbl.replace best_w u.nodes.(i) w;
              u.fwd.(i) |> KMap.iter (fun u w1 ->
                  let w2, _, u, ui = repr g u in
                  let w = W.(w + w1 + w2) in
                  if u == v then begin
                    if W.(w + DistMat.dist ui vi u.dists <= w0) then raise Found
                  end else if topo_compare u v < 1 then Queue.push (u, ui, w) todo)
            end
          done
        end
      done; assert false
      with
      | Queue.Empty -> false
      | Found -> true
    end

  (* Uncomment to debug the cycle detection algorithm. *)
  (* let insert_edge u w v g =
   *   let check_invariants = check_invariants ~required_canonical:(fun _ -> false) in
   *   check_invariants g;
   *   let g = insert_edge u w v g in
   *   check_invariants g;
   *   assert (search_path u w v g);
   *   g *)

  let check_shift g u w v =
    if Point.equal u v then W.(w = W.zero)
    else
      let uw, u = repr_shift g (Key.of_point u g.table) in
      let vw, v = repr_shift g (Key.of_point v g.table) in
      Key.equal u v && W.(uw - vw = w)

  let check g u w v =
    if Point.equal u v then W.(W.zero <= w)
    else search_path (Key.of_point u g.table) w (Key.of_point v g.table) g

  (* enforce_shift g u w v will force u=v+w if possible, will fail otherwise *)
  let enforce_shift u w v g =
    let err_uv () = explained_error u Eq w v g in
    let err_vu () = explained_error v Eq W.(-w) u g in
    let wu, u, uc, _ = repr g (Key.of_point u g.table) in
    let wv, v, vc, _ = repr g (Key.of_point v g.table) in
    let w = W.(w - wu + wv) in
    if Key.equal u v then
      if W.(w = zero) then g else err_uv ()
    else if topo_compare uc vc = 1 then
      let g = insert_edge v W.(-w) u g in  (* Cannot fail *)
      try insert_edge u w v g with Inconsistent -> err_uv ()
    else
      (* May fail if uc = vc *)
      let g = try insert_edge u w v g with Inconsistent -> err_uv () in
      try insert_edge v W.(-w) u g with Inconsistent -> err_vu ()

  (* enforce g u w v will force u<=v+w if possible, will fail otherwise *)
  let enforce u w v g =
    try insert_edge (Key.of_point u g.table) w (Key.of_point v g.table) g
    with Inconsistent -> explained_error u Le w v g

  let empty = { entries = KMap.empty; index = -1; table = Key.empty }

  (* Normalization *)
  let constraints_of g =
    let to_point x = Key.to_point x g.table in
    let parts = KHashtbl.create 32 in
    let add_part u w v =
      let m = try KHashtbl.find parts v with Not_found -> Point.Map.empty in
      KHashtbl.replace parts v (Point.Map.add (to_point u) w m)
    in
    let csts = ref Constraints.empty in
    g.entries |> KMap.iter (fun u a ->
        match a with
        | SccHead ({nodes; dists; fwd; _}, _) ->
          let n = Array.length nodes in
          for i = 0 to n - 1 do
            let u = to_point nodes.(i) in
            for j = 0 to n - 1 do
              if i <> j then
                csts := Constraints.add (u, Le, DistMat.dist i j dists,
                                         to_point nodes.(j)) !csts
            done;
            fwd.(i) |> KMap.iter (fun v w ->
                csts := Constraints.add  (u, Le, w, to_point v) !csts);
            add_part nodes.(i) W.zero nodes.(i)
          done
        | SccOf _ -> ()
        | Shift (w, v) ->
          let w', v = repr_shift g v in
          add_part u W.(-w-w') v);
    !csts, KHashtbl.fold (fun _ x acc -> x::acc) parts []

  (* domain g.entries = kept + removed *)
  let constraints_for ~kept g =
    let csts = ref Constraints.empty in
    let add_constraint u kind w v =
      csts := Constraints.add (Key.to_point u g.table, kind, w, Key.to_point v g.table) !csts
    in
    let kept = Point.Set.fold (fun u accu -> KSet.add (Key.of_point u g.table) accu) kept KSet.empty in
    (* rmap: partial map from canonical shifted points to kept points with weight *)
    let rmap = KSet.fold (fun u rmap ->
        let w, ucan = repr_shift g u in
        if KSet.mem ucan kept then begin
            if not (Key.equal u ucan) then add_constraint u Eq w ucan;
            KMap.add ucan (W.zero, ucan) rmap
        end else
          match KMap.find_opt ucan rmap with
          | Some (w', v) -> add_constraint u Eq W.(w+w') v; rmap
          | None -> KMap.add ucan (W.(-w), u) rmap)
      kept KMap.empty
    in

    kept |> KSet.iter (fun u0 ->
      let uw, u = repr_shift g u0 in
      if Key.equal (snd (KMap.find u rmap)) u0 then begin
        let todo = ref TMap.empty in
        let push_todo v w =
          let vw, v, vc, vi = repr g v in
          let w = W.(w + vw) in
          todo := !todo |> TMap.update vc (function
              | Some vcw -> vcw.(vi) <- W.min vcw.(vi) w; Some vcw
              | None ->
                 let vcw = Array.make (Array.length vc.nodes) W.inf in
                 vcw.(vi) <- w;
                 Some vcw)
        in
        push_todo u uw;
        while not (TMap.is_empty !todo) do
          let vc, vcw = TMap.min_binding !todo in todo := TMap.remove vc !todo;
          let n = Array.length vcw in
          let dist a b = DistMat.dist a b vc.dists in
          let d = Array.make n W.inf in
          for i = 0 to n - 1 do
            if W.(vcw.(i) < inf) then
              for j = 0 to n - 1 do
                d.(j) <- W.(min (vcw.(i) + dist i j) d.(j))
              done
          done;
          for i = 0 to n - 1 do
            let exception Implied in
            try
              for j = 0 to n - 1 do
                if i <> j && not (Key.equal vc.nodes.(j) u) &&
                   W.(d.(j) + dist j i = d.(i)) && KMap.mem vc.nodes.(j) rmap
                then raise Implied
              done;
              match if Key.equal vc.nodes.(i) u then None else KMap.find_opt vc.nodes.(i) rmap with
              | Some (w', v') -> add_constraint u0 Le W.(d.(i) + w') v'
              | None ->
                vc.fwd.(i) |> KMap.iter (fun v' wv' -> push_todo v' W.(d.(i) + wv'))
            with Implied -> ()
          done
        done
      end);
    !csts

  let domain g =
    KMap.fold (fun u _ acc -> Point.Set.add (Key.to_point u g.table) acc)
      g.entries Point.Set.empty

  let model g =
    let vals =
      ref (g.entries
           |> KMap.filter (fun _ -> function Shift _ -> false | _ -> true)
           |> KMap.map (fun _ -> W.zero))
    in
    let min_val u l = vals := !vals |> KMap.modify u (fun _ l' -> W.min l l') in
    KMap.fold (fun _ x acc -> match x with SccHead (c, _) -> c::acc | _ -> acc) g.entries []
    |> List.sort topo_compare
    |> List.iter (fun c ->
       let n = Array.length c.nodes in
       for j = 0 to n - 1 do
         for i = 0 to n - 1 do
           if i <> j then
             min_val c.nodes.(j)
               W.(KMap.find c.nodes.(i) !vals + DistMat.dist i j c.dists)
         done;
         c.fwd.(j) |> KMap.iter (fun v w ->
           let wv, v = repr_shift g v in
           min_val v W.(KMap.find c.nodes.(j) !vals + w + wv))
       done);
    g.entries |> KMap.iter (fun u -> function
                     | Shift (w, v) ->
                        let wv, v = repr_shift g v in
                        vals := KMap.add u W.(w + wv + KMap.find v !vals) !vals
                     | _ -> ());
    KMap.fold (fun u w acc -> Point.Map.add (Key.to_point u g.table)
                                (-W.to_int w) acc) !vals Point.Map.empty

  let choose p g u =
    let exception Found of (constraint_weight * Point.t) in
    try
      let wru, ru = repr_shift g (Key.of_point u g.table) in
      let rup = Key.to_point ru g.table in
      if p rup then raise (Found (wru, rup));
      g.entries |> KMap.iter (fun v -> function
          | SccHead _ | SccOf _ -> () (* we already tried [p ru] *)
          | Shift (w, v') ->
            let wrv, rv = repr_shift g v' in
            if Key.equal rv ru then
              let v = Key.to_point v g.table in
              if p v then raise (Found (W.(wru - (w + wrv)), v))
              (* NB: we could also try [p v'] but it will come up in the
                 rest of the iteration regardless. *)
        );
      None
    with Found p -> Some p

  type node = Alias of W.t * Point.t | Node of W.t Point.Map.t
  type repr = node Point.Map.t

  let repr g =
    let add u x m = Point.Map.add (Key.to_point u g.table) x m in
    let r = ref Point.Map.empty in
    g.entries |> KMap.iter (fun _ -> function
        | SccHead (n, _) ->
          for i = 0 to Array.length n.nodes - 1 do
            let adj = ref Point.Map.empty in
            n.fwd.(i) |> KMap.iter (fun u w -> adj := add u w !adj);
            for j = 0 to Array.length n.nodes - 1 do
              if i <> j then adj := add n.nodes.(j) (DistMat.dist i j n.dists) !adj
            done;
            r := add n.nodes.(i) (Node !adj) !r
          done
        | Shift (w, u) -> r := add u (Alias (w, Key.to_point u g.table)) !r
        | SccOf _ -> ());
    !r
end
