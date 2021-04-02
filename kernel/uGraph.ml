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

module G = AcyclicGraph.Make(struct
    type t = Level.t
    module Set = LSet
    module Map = LMap
    module Constraint = Constraint

    let source = Level.set

    let equal = Level.equal
    let compare = Level.compare

    type explanation = Univ.explanation
    let error_inconsistency d u v p =
      raise (UniverseInconsistency (d,Universe.make u, Universe.make v, p))

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

let check_smaller_expr g (u,n) k (v,m) =
  let diff = k + (n - m) in
  G.check_leq g.graph u diff v

let exists_bigger g ul n l =
  Universe.exists (fun ul' ->
    check_smaller_expr g ul n ul') l

let real_check_leq g u n v =
  Universe.for_all (fun ul -> exists_bigger g ul n v) u

let check_leq g u n v =
  type_in_type g ||
  (Universe.equal u v && n <= 0) || (g.sprop_cumulative && Universe.is_sprop u && n = 0) ||
  (not (Universe.is_sprop u) && not (Universe.is_sprop v) &&
    ((is_type0m_univ u && n = 0) ||
     real_check_leq g u n v))

let check_eq g u v =
  type_in_type g ||
  Universe.equal u v ||
  (not (Universe.is_sprop u || Universe.is_sprop v) &&
   (real_check_leq g u 0 v && real_check_leq g v 0 u))

let check_eq_level g u v =
  u == v ||
  type_in_type g ||
  (not (Level.is_sprop u || Level.is_sprop v) && G.check_eq g.graph u 0 v)

let empty_universes = {graph=G.empty; sprop_cumulative=false; type_in_type=false}

let initial_universes =
  let big_rank = 1000000 in
  let g = G.empty in
  let g = G.add ~rank:big_rank Level.prop g in
  let g = G.add ~rank:big_rank Level.set g in
  {empty_universes with graph=G.enforce_leq Level.prop 1 Level.set g}

let initial_universes_with g = {g with graph=initial_universes.graph}

let enforce_constraint (u,d,v) g =
  match d with
  | Le n -> G.enforce_leq u n v g
  | Eq n -> G.enforce_eq u n v g

let enforce_constraint (u,d,v as cst) g =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> g_map (enforce_constraint cst) g
  | true, (Eq 0|Le 0), true -> g
  | true, Le 0, false when g.sprop_cumulative -> g
  | _ ->  raise (UniverseInconsistency (d,Universe.make u, Universe.make v, None))

let enforce_constraint cst g =
  if not (type_in_type g) then enforce_constraint cst g
  else try enforce_constraint cst g with UniverseInconsistency _ -> g

let merge_constraints csts g = Constraint.fold enforce_constraint csts g

let check_constraint g (u,d,v) =
  match d with
  | Le n -> G.check_leq g u n v
  | Eq n -> G.check_eq g u n v

let check_constraint g (u,d,v as cst) =
  match Level.is_sprop u, d, Level.is_sprop v with
  | false, _, false -> check_constraint g.graph cst
  | true, (Eq 0|Le 0), true -> true
  | true, Le 0, false -> g.sprop_cumulative || type_in_type g
  | _ -> type_in_type g

let check_constraints csts g = Constraint.for_all (check_constraint g) csts

let leq_expr (u,m) (v,n) =
  (u,Le (m - n),v)

let enforce_leq_alg u v g =
  let open Util in
  let enforce_one (u,v) = function
    | Inr _ as orig -> orig
    | Inl (cstrs,g) as orig ->
      if check_smaller_expr g u 0 v then orig
      else
        (let c = leq_expr u v in
         match enforce_constraint c g with
         | g -> Inl (Constraint.add c cstrs,g)
         | exception (UniverseInconsistency _ as e) -> Inr e)
  in
  (* max(us) <= max(vs) <-> forall u in us, exists v in vs, u <= v *)
  let c = List.map (fun u -> List.map (fun v -> (u,v)) (Universe.repr v)) (Universe.repr u) in
  let c = List.cartesians enforce_one (Inl (Constraint.empty,g)) c in
  (* We pick a best constraint: smallest number of constraints, not an error if possible. *)
  let order x y = match x, y with
    | Inr _, Inr _ -> 0
    | Inl _, Inr _ -> -1
    | Inr _, Inl _ -> 1
    | Inl (c,_), Inl (c',_) ->
      Int.compare (Constraint.cardinal c) (Constraint.cardinal c')
  in
  match List.min order c with
  | Inl x -> x
  | Inr e -> raise e

(*let enforce_leq_alg u ve g =
  Feedback.msg_debug Pp.(hov 2 (str"enforce_leq_alg " ++ Universe.pr u ++ str" and " ++ Universe.pr ve));
  try
     let r = enforce_leq_alg u ve g in
     Feedback.msg_debug Pp.(str "succeeded");
     r
  with e ->
    Feedback.msg_debug Pp.(str"inconsistent");
    raise e*)


let enforce_leq_alg u v g =
  match Universe.is_sprop u, Universe.is_sprop v with
  | true, true -> Constraint.empty, g
  | false, false -> enforce_leq_alg u v g
  | left, _ ->
    if left && g.sprop_cumulative then Constraint.empty, g
    else raise (UniverseInconsistency (Le 0, u, v, None))

(* sanity check wrapper *)
let enforce_leq_alg u v g =
  let _,g as cg = enforce_leq_alg u v g in
  assert (check_leq g u 0 v);
  cg

module Bound =
struct
  type t = Prop | Set
end

exception AlreadyDeclared = G.AlreadyDeclared
let add_universe u ~lbound ~strict g =
  let lbound = match lbound with Bound.Prop -> Level.prop | Bound.Set -> Level.set in
  let graph = G.add u g.graph in
  let d = if strict then Le 1 else Le 0 in
  enforce_constraint (lbound,d,u) {g with graph}

let add_universe_unconstrained u g = {g with graph=G.add u g.graph}

exception UndeclaredLevel = G.Undeclared
let check_declared_universes g l = G.check_declared g.graph (LSet.remove Level.sprop l)

let constraints_of_universes g = G.constraints_of g.graph
let constraints_for ~kept g = G.constraints_for ~kept:(LSet.remove Level.sprop kept) g.graph

(** Subtyping of polymorphic contexts *)

let check_subtype ~lbound univs ctxT ctx =
  if AUContext.size ctxT == AUContext.size ctx then
    let (inst, cst) = UContext.dest (AUContext.repr ctx) in
    let cstT = UContext.constraints (AUContext.repr ctxT) in
    let push accu v = add_universe v ~lbound ~strict:false accu in
    let univs = Array.fold_left push univs (Instance.to_array inst) in
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
          (Int.equal i (Array.length t1)) || (check_eq_level g t1.(i) t2.(i) && aux (i + 1))
        in aux 0)

let domain g = LSet.add Level.sprop (G.domain g.graph)
let choose p g u = if Level.is_sprop u
  then if p u then Some u else None
  else G.choose p g.graph u

let check_universes_invariants g = G.check_invariants ~required_canonical:Level.is_small g.graph

(** Pretty-printing *)

let pr_pmap sep pr map =
  let cmp (u,_) (v,_) = Level.compare u v in
  Pp.prlist_with_sep sep pr (List.sort cmp (LMap.bindings map))

let pr_pset sep pr map =
  let cmp = Level.compare in
  Pp.prlist_with_sep sep pr (List.sort cmp (LSet.elements map))

let pr_incr n =
  let open Pp in
  if Int.equal n 0 then mt()
  else if n < 0 then str"- " ++ int (-n)
  else str"+ " ++ int n

let pr_arc prl = let open Pp in
  function
  | u, (uw, G.Node (ltle, gtge)) ->
    if LMap.is_empty ltle && LSet.is_empty gtge then mt ()
    else
      prl u ++ pr_incr uw ++ str " " ++
      v 0
        (pr_pmap spc (fun (v, weight) -> pr_weight_arc (Le weight) (prl v))
            ltle) ++
      v 0
        (pr_pset spc (fun v -> prl v ++ pr_weight_arc (Le 0) (prl u))
            gtge) ++
      fnl ()
  | u, (uw, G.Alias (v, vw)) -> (* u + uw = v + n *)
    if (vw - uw) < 0 then
      prl v  ++ str " = " ++ prl u ++ pr_incr (uw - vw) ++ fnl ()
    else
      prl u  ++ str " = " ++ prl v ++ pr_incr (vw - uw) ++ fnl ()


type node = G.node =
| Alias of Level.t * int
| Node of int LMap.t * LSet.t

let repr g = G.repr g.graph

let pr_universes prl g = pr_pmap Pp.mt (pr_arc prl) g
