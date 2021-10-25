(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

let error_inconsistency u d w v p =
  raise (UniverseInconsistency (d,Universe.make u,
    (Universe.addn (AcyclicGraph.int_of_weight w) (Universe.make v)), p))

module G = AcyclicGraph.Make(struct
    type t = Level.t
    module Set = Level.Set
    module Map = Level.Map
    module Constraints = Constraints

    let equal = Level.equal
    let compare = Level.compare

    type explanation = (constraint_type * constraint_weight * Level.t) list
    let error_inconsistency = error_inconsistency
    let pr = Level.pr
  end) [@@inlined] (* without inline, +1% ish on HoTT, compcert. See jenkins 594 vs 596 *)
(* Do not include G to make it easier to control universe specific
   code (eg add_universe with a constraint vs G.add with no
   constraint) *)

type t = {
  graph: G.t;
  sprop_cumulative : bool;
  type_in_type : bool;
}

type 'a check_function = t -> 'a -> 'a -> bool

let g_map f g =
  let g' = f g.graph in
  if g.graph == g' then g
  else {g with graph=g'}

let set_cumulative_sprop b g = {g with sprop_cumulative=b}

let set_type_in_type b g = {g with type_in_type=b}

let type_in_type g = g.type_in_type

let check_leq_level g u v =
  type_in_type g ||
  Level.equal u v || (g.sprop_cumulative && Level.is_sprop u) ||
  (not (Level.is_sprop u) && not (Level.is_sprop v) &&
    (Level.is_prop u || G.check g.graph u AcyclicGraph.weight_le v))


let check_leq_expr g (u,n) (v,m) =
  G.check g.graph u (AcyclicGraph.weight_of_int (m - n)) v

let check_leq_level_expr g u v =
  type_in_type g ||
  LevelExpr.leq u v || (g.sprop_cumulative && LevelExpr.is_sprop u) ||
  (not (LevelExpr.is_sprop u) && not (LevelExpr.is_sprop v) &&
    (LevelExpr.is_prop u || check_leq_expr g u v))

let exists_bigger g ul l =
  Universe.exists (fun ul' -> check_leq_expr g ul ul') l

let real_check_leq g u v =
  Universe.for_all (fun ul -> exists_bigger g ul v) u

let check_leq g u v =
  type_in_type g ||
  Universe.equal u v || (g.sprop_cumulative && Universe.is_sprop u) ||
  (not (Universe.is_sprop u) && not (Universe.is_sprop v) &&
    (is_type0m_univ u ||
     real_check_leq g u v))

let check_eq g u v =
  type_in_type g ||
  Universe.equal u v ||
  (not (Universe.is_sprop u || Universe.is_sprop v) &&
   (real_check_leq g u v && real_check_leq g v u))

let check_eq_expr graph (u, w) (v, w') =
  G.check_shift graph u (AcyclicGraph.weight_of_int (w' - w)) v

let check_eq_level_expr g u v =
  u == v ||
  type_in_type g ||
  LevelExpr.equal u v ||
  (not (LevelExpr.is_sprop u || LevelExpr.is_sprop v) &&
  check_eq_expr g.graph u v)

let check_eq_level g u v =
  u == v ||
  type_in_type g ||
  (not (Level.is_sprop u || Level.is_sprop v) &&
  G.check_shift g.graph u AcyclicGraph.weight_le v)

let empty_universes = {graph=G.empty; sprop_cumulative=false; type_in_type=false}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.prop g in
  let g = G.add ~rank:big_rank Level.set g in
  {empty_universes with graph = G.enforce Level.prop AcyclicGraph.weight_lt Level.set g}

let initial_universes_with g = {g with graph=initial_universes.graph}

let _univs_flag, debug_univs = CDebug.create_full ~name:"universes" ()

let enforce_constraint (u,d,w,v as cstr) g =
  debug_univs (fun () -> Pp.(str "Enforcing constraint: " ++ Univ.pr_constraint Level.pr cstr));
  let g' =
  match d with
  | AcyclicGraph.Le -> G.enforce u w v g
  | AcyclicGraph.Eq -> G.enforce_shift u w v g
  in
  g'

let enforce_constraint_key = CProfile.declare_profile "enforce_constraint"
let enforce_constraint a b = CProfile.profile2 enforce_constraint_key enforce_constraint a b


let enforce_constraint (u,d,w,v as cst) g =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> g_map (enforce_constraint cst) g
  | true, _, true when w >= 0 -> g
  | true, AcyclicGraph.Le, false when g.sprop_cumulative -> g
  | _ -> error_inconsistency u d w v None

let enforce_constraint cst g =
  if not (type_in_type g) then enforce_constraint cst g
  else try enforce_constraint cst g with UniverseInconsistency _ -> g

let merge_constraints csts g = Constraints.fold enforce_constraint csts g

let check_constraint g (u,d,w,v) =
  match d with
  | AcyclicGraph.Le -> G.check g u w v
  | AcyclicGraph.Eq -> G.check_shift g u w v

let check_constraint g (u,d,w,v as cst) =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> check_constraint g.graph cst
  | true, (AcyclicGraph.Eq|AcyclicGraph.Le), true -> w >= 0
  | true, AcyclicGraph.Le, false -> g.sprop_cumulative || type_in_type g
  | _ -> type_in_type g

let check_constraints csts g = Constraints.for_all (check_constraint g) csts

let enforce_leq_alg u v g =
  let open Util in
  let enforce_one (u,v) = function
    | Inr _ as orig -> orig
    | Inl (cstrs,g) as orig ->
      if check_leq_level_expr g u v then orig
      else
        (let c = mk_constraint u AcyclicGraph.Le v in
         match enforce_constraint c g with
         | g -> Inl (Constraints.add c cstrs,g)
         | exception (UniverseInconsistency _ as e) -> Inr e)
  in
  (* max(us) <= max(vs) <-> forall u in us, exists v in vs, u <= v *)
  let c = List.map (fun u -> List.map (fun v -> (u,v)) (Universe.repr v)) (Universe.repr u) in
  let c = List.cartesians enforce_one (Inl (Constraints.empty,g)) c in
  (* We pick a best constraint: smallest number of constraints, not an error if possible. *)
  let order x y = match x, y with
    | Inr _, Inr _ -> 0
    | Inl _, Inr _ -> -1
    | Inr _, Inl _ -> 1
    | Inl (c,_), Inl (c',_) ->
      Int.compare (Constraints.cardinal c) (Constraints.cardinal c')
  in
  match List.min order c with
  | Inl x -> x
  | Inr e -> raise e

let enforce_leq_alg u v g =
  match Universe.is_sprop u, Universe.is_sprop v with
  | true, true -> Constraints.empty, g
  | false, false -> enforce_leq_alg u v g
  | left, _ ->
    if left && g.sprop_cumulative then Constraints.empty, g
    else raise (UniverseInconsistency (AcyclicGraph.Le, u, v, None))

(* sanity check wrapper *)
let enforce_leq_alg u v g =
  let _,g as cg = enforce_leq_alg u v g in
  assert (check_leq g u v);
  cg

module Bound =
struct
  type t = Prop | Set
end

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~lbound ~strict g =
  let lbound = match lbound with Bound.Prop -> Level.prop | Bound.Set -> Level.set in
  let graph = G.add u g.graph in
  let d = AcyclicGraph.Le in
  let w = if strict then AcyclicGraph.weight_lt else AcyclicGraph.weight_le in
  enforce_constraint (lbound,d,w,u) {g with graph}

let add_universe_unconstrained u g = {g with graph=G.add u g.graph}

exception UndeclaredLevel = G.Undeclared
let check_declared_universes g l = G.check_declared g.graph (Level.Set.remove Level.sprop l)

let constraints_of_universes g = G.constraints_of g.graph
let constraints_for ~kept g = G.constraints_for ~kept:(Level.Set.remove Level.sprop kept) g.graph

(** Subtyping of polymorphic contexts *)

let check_subtype ~lbound univs ctxT ctx =
  if AbstractContext.size ctxT == AbstractContext.size ctx then
    let uctx = AbstractContext.repr ctx in
    let inst = UContext.abstraction uctx in
    let cst = UContext.constraints uctx in
    let cstT = UContext.constraints (AbstractContext.repr ctxT) in
    let push accu v = add_universe v ~lbound ~strict:false accu in
    let univs = Array.fold_left push univs (LevelAbstraction.to_array inst) in
    let univs = merge_constraints cstT univs in
    check_constraints cst univs
  else false

(** Instances *)

let check_eq_instances g t1 t2 =
  let t1 = Instance.to_array t1 in
  let t2 = Instance.to_array t2 in
  t1 == t2 ||
    (Int.equal (Array.length t1) (Array.length t2) &&
        let rec aux i =
          (Int.equal i (Array.length t1)) || (check_eq_level_expr g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

let domain g = Level.Set.add Level.sprop (G.domain g.graph)
let choose p g u = if Level.is_sprop u
  then if p u then Some (LevelExpr.make u) else None
  else
    (G.choose p g.graph u) |>
    Option.map (fun (w, l) -> LevelExpr.make ~weight:(AcyclicGraph.int_of_weight w) l)

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_small g.graph

(** Pretty-printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (Level.Map.bindings map))

let pr_arc prl = let open Pp in
  function
  | u, G.Node ltle ->
    if Level.Map.is_empty ltle then mt ()
    else
      prl u ++ str " " ++
      v 0 (pr_pmap spc (fun (v, w) ->str "<= " ++ prl v ++ pr_increment w) ltle) ++
      fnl ()
  | u, G.Alias (w, v) ->
    prl u  ++ str " = " ++ prl v ++ pr_increment w ++ fnl ()

type node = G.node =
| Alias of AcyclicGraph.constraint_weight * Level.t
| Node of AcyclicGraph.constraint_weight Level.Map.t

let repr g = G.repr g.graph

let pr_universes prl g = pr_pmap Pp.mt (pr_arc prl) g
