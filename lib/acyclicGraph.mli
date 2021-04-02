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

module Make (Point:Point) : sig

  type t

  val empty : t

  val check_invariants : required_canonical:(Point.t -> bool) -> t -> unit

  exception AlreadyDeclared
  val add : ?rank:int -> Point.t -> t -> t
  (** All points must be pre-declared through this function before
     they can be mentioned in the others. NB: use a large [rank] to
     keep the node canonical *)

  exception Undeclared of Point.t
  val check_declared : t -> Point.Set.t -> unit
  (** @raise Undeclared if one of the points is not present in the graph. *)

  type 'a check_function = t -> 'a -> int -> 'a -> bool

  val check_eq : Point.t check_function
  val check_leq : Point.t check_function

  val enforce_eq : Point.t -> int -> Point.t -> t -> t
  val enforce_leq : Point.t -> int -> Point.t -> t -> t

  val constraints_of : t -> Point.Constraint.t * Point.Set.t list

  val constraints_for : kept:Point.Set.t -> t -> Point.Constraint.t

  val domain : t -> Point.Set.t

  val choose : (Point.t -> bool) -> t -> Point.t -> Point.t option

  (** {5 High-level representation} *)

  type node =
  | Alias of Point.t * int (* A node v s.t. u = v + n *)
  | Node of int Point.IMap.t (* Nodes v s.t. u + n <= v *)
    * Point.Set.t (* Nodes lower than u in the same component *)
  type repr = node Point.IMap.t
  val repr : t -> repr

end
