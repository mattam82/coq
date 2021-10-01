(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Graphs representing strict orders *)

type constraint_weight
val weight_le : constraint_weight (* 0 *)
val weight_lt : constraint_weight (* -1 *)
val weight_of_int : int -> constraint_weight

type constraint_type = Eq | Le

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  (* TODO : we should reduce ambiguity in constraints sets by
     - not inserting Eq constraints (instead use a pair of Le constraints)
     - use a map from pairs of points to weight, so that we cannot have edges
       of different weights between the same pair of points. *)
  module Constraints : CSet.S with type elt = (t * constraint_type * constraint_weight * t)

  val equal : t -> t -> bool
  val compare : t -> t -> int

  type explanation = (constraint_type * constraint_weight * t) list
  val error_inconsistency :
    t -> t -> constraint_type -> constraint_weight -> explanation lazy_t option -> 'a

  val pr : t -> Pp.t
end

module Make (Point:Point) : sig

  type t

  val empty : t

  val check_invariants : required_canonical:(Point.t -> bool) -> t -> unit

  exception AlreadyDeclared
  val add : ?rank:int -> Point.t -> t -> t
  (** All points must be pre-declared through this function before
     they can be mentioned in the others. NB: use a large [rank] to
     keep the node canonical *)

  (** [add_shift x y w g] Adds x as a shifted alias for y. I.e., we then
     have x = y + w. *)
  val add_shift : Point.t -> constraint_weight -> Point.t -> t -> t

  exception Undeclared of Point.t
  val check_declared : t -> Point.Set.t -> unit
  (** @raise Undeclared if the points is not present in the graph. *)

  val check_shift : t -> Point.t -> constraint_weight -> Point.t -> bool

  val check : t -> Point.t -> constraint_weight -> Point.t -> bool

  val enforce_shift : Point.t-> constraint_weight -> Point.t -> t -> t

  val enforce : Point.t -> constraint_weight -> Point.t -> t -> t

  val constraints_of : t -> Point.Constraints.t * constraint_weight Point.Map.t list

  val constraints_for : kept:Point.Set.t -> t -> Point.Constraints.t

  val domain : t -> Point.Set.t

  val choose : (Point.t -> bool) -> t -> Point.t ->
               (constraint_weight * Point.t) option

  (** {5 High-level representation} *)

  type node =
  | Alias of constraint_weight * Point.t
  | Node of constraint_weight Point.Map.t
  type repr = node Point.Map.t
  val repr : t -> repr

end
