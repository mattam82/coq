(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ

(** {6 Graphs of universes. } *)

type t

type universes = t

type 'a check_function = universes -> 'a -> 'a -> bool
val check_leq : universe check_function
val check_eq : universe check_function

(** The empty graph of universes *)
val empty_universes : universes

(** The initial graph of universes: Prop < Set *)
val initial_universes : universes

val is_initial_universes : universes -> bool

val sort_universes : universes -> universes

(** Adds a universe to the graph, ensuring it is >= or > Set.
   @raises AlreadyDeclared if the level is already declared in the graph. *)

exception AlreadyDeclared

val add_universe : universe_level_name -> bool -> universes -> universes

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

val enforce_constraint : Level.t univ_constraint -> universes -> universes
val merge_constraints : constraints -> universes -> universes

val constraints_of_universes : universes -> constraints

val check_constraint  : universes -> Level.t univ_constraint -> bool
val check_constraints : constraints -> universes -> bool

val check_eq_instances : Instance.t check_function
(** Check equality of instances w.r.t. a universe graph *)

(** {6 Pretty-printing of universes. } *)

val pr_universes : (LevelName.t -> Pp.std_ppcmds) -> universes -> Pp.std_ppcmds

module LESet : sig
  include CSig.SetS with type elt = universe_level
end
val lower_universes : universes -> Level.t -> LESet.t
                                                                 
(** {6 Dumping to a file } *)

val dump_universes :
  (constraint_type -> string -> string -> unit) ->
  universes -> unit
