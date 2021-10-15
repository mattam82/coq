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

type t =
  | ULe of Universe.t * Universe.t
  | UEq of Universe.t * Universe.t
  | ULub of LevelExpr.t * LevelExpr.t
  | UWeak of LevelExpr.t * LevelExpr.t


let is_trivial = function
  | ULe (u, v) | UEq (u, v) -> Universe.equal u v
  | ULub (u, v) | UWeak (u, v) -> LevelExpr.equal u v

let force = function
  | ULe _ | UEq _ | UWeak _ as cst -> cst
  | ULub (u,v) -> UEq (Universe.tip u, Universe.tip v)

let check g = function
  | ULe (u,v) -> UGraph.check_leq g u v
  | UEq (u,v) -> UGraph.check_eq g u v
  | ULub (u,v) -> UGraph.check_eq_level_expr g u v
  | UWeak _ -> true

let pr_with prl = let open Pp in function
  | ULe (u, v) -> Universe.pr_with prl u ++ str " <= " ++ Universe.pr_with prl v
  | UEq (u, v) -> Universe.pr_with prl u ++ str " = " ++ Universe.pr_with prl v
  | ULub (u, v) -> LevelExpr.pr_with prl u ++ str " /\\ " ++ LevelExpr.pr_with prl v
  | UWeak (u, v) -> LevelExpr.pr_with prl u ++ str " ~ " ++ LevelExpr.pr_with prl v

module Set = struct
  module S = Set.Make(
  struct
    type nonrec t = t

    let compare x y =
      match x, y with
      | ULe (u, v), ULe (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else i
      | UEq (u, v), UEq (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else if Universe.equal u v' && Universe.equal v u' then 0
        else i
      | ULub (u, v), ULub (u', v') | UWeak (u, v), UWeak (u', v') ->
        let i = LevelExpr.compare u u' in
        if Int.equal i 0 then LevelExpr.compare v v'
        else if LevelExpr.equal u v' && LevelExpr.equal v u' then 0
        else i
      | ULe _, _ -> -1
      | _, ULe _ -> 1
      | UEq _, _ -> -1
      | _, UEq _ -> 1
      | ULub _, _ -> -1
      | _, ULub _ -> 1
  end)

  include S

  let add cst s =
    if is_trivial cst then s
    else add cst s

  let pr prl c =
    let open Pp in
    fold (fun cst pp_std ->
        pp_std ++ pr_with prl cst ++ fnl ()) c (str "")

  let equal x y =
    x == y || equal x y

  let force s = map force s

  let check g s = for_all (check g) s
end

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

let enforce_eq_instances_univs strict x y c =
  let mk u v = if strict then ULub (u, v) else UEq (Universe.tip u, Universe.tip v) in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly Pp.(str "Invalid argument: enforce_eq_instances_univs called with" ++
                          str " instances of different lengths.");
    CArray.fold_right2
      (fun x y -> Set.add (mk x y))
      ax ay c
