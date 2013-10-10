(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   The features of the Proof module are undoing and focusing.
   A proof is a mutable object, it contains a proofview, and some information
   to be able to undo actions, and to unfocus the current view. All three
   of these being meant to evolve.
   - Proofview: a proof is primarily the data of the current view.
     That which is shown to the user (as a remainder, a proofview
     is mainly the logical state of the proof, together with the
     currently focused goals).
   - Focus: a proof has a focus stack: the top of the stack contains
     the context in which to unfocus the current view to a view focused
     with the rest of the stack.
     In addition, this contains, for each of the focus context,  a 
     "focus kind" and a "focus condition" (in practice, and for modularity,
     the focus kind is actually stored inside the condition). To unfocus, one
     needs to know the focus kind, and the condition (for instance "no condition" or
     the proof under focused must be complete) must be met.
   - Undo: since proofviews and focus stacks are immutable objects, 
     it could suffice to hold the previous states, to allow to return to the past.
     However, we also allow other modules to do actions that can be undone.
     Therefore the undo stack stores action to be ran to undo.
*)

open Term

(* Type of a proof. *)
type proof

(* Returns a stylised view of a proof for use by, for instance,
   ide-s. *)
(* spiwack: the type of [proof] will change as we push more refined
   functions to ide-s. This would be better than spawning a new nearly
   identical function everytime. Hence the generic name. *)
(* In this version: returns the focused goals, a representation of the
   focus stack (the number of goals at each level) and the underlying
   evar_map *)
val proof : proof -> Goal.goal list * (Goal.goal list * Goal.goal list) list * Evd.evar_map

(*** General proof functions ***)

val start : (Environ.env * Term.types Univ.in_universe_context_set) list -> proof
val initial_goals : proof -> (Term.constr * Term.types) list

(* Returns [true] if the considered proof is completed, that is if no goal remain
    to be considered (this does not require that all evars have been solved). *)
val is_done : proof -> bool

(* Returns the list of partial proofs to initial goals. *)
val partial_proof : proof -> Term.constr list

(* Returns the proofs (with their type) of the initial goals.
    Raises [UnfinishedProof] is some goals remain to be considered.
    Raises [HasUnresolvedEvar] if some evars have been left undefined. *)
exception UnfinishedProof
exception HasUnresolvedEvar
val return : proof -> Evd.evar_map

(*** Focusing actions ***)

(* ['a focus_kind] is the type used by focusing and unfocusing
    commands to synchronise. Focusing and unfocusing commands use
    a particular ['a focus_kind], and if they don't match, the unfocusing command
    will fail.
    When focusing with an ['a focus_kind], an information of type ['a] is
    stored at the focusing point. An example use is the "induction" tactic
    of the declarative mode where sub-tactics must be aware of the current
    induction argument. *)
type 'a focus_kind
val new_focus_kind : unit -> 'a focus_kind

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.
    Conditions always carry a focus kind, and inherit their type parameter
    from it.*)
type 'a focus_condition 
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind].
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{- solve_goal. }] because they use a loose-end condition. *)
val no_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete.
   If [loose_end] (default [false]) is [true], then if the [focus_kind]
   doesn't match, then unfocusing can occur, provided it unfocuses
   an earlier focus.
   For instance bullets can be unfocused in the following situation
   [{ - solve_goal. }] because they use a loose-end condition.  *)
val done_cond : ?loose_end:bool -> 'a focus_kind -> 'a focus_condition

(* focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
val focus : 'a focus_condition -> 'a -> int -> proof -> proof

exception FullyUnfocused
exception CannotUnfocusThisWay
(* Unfocusing command.
   Raises [FullyUnfocused] if the proof is not focused.
   Raises [CannotUnfocusThisWay] if the proof the unfocusing condition
     is not met. *)
val unfocus : 'a focus_kind -> proof -> unit -> proof

(* [unfocused p] returns [true] when [p] is fully unfocused. *)
val unfocused : proof -> bool

(* [get_at_focus k] gets the information stored at the closest focus point
    of kind [k].
    Raises [NoSuchFocus] if there is no focus point of kind [k]. *)
exception NoSuchFocus
val get_at_focus : 'a focus_kind -> proof -> 'a

(* [is_last_focus k] check if the most recent focus is of kind [k] *)
val is_last_focus : 'a focus_kind -> proof -> bool

(* returns [true] if there is no goal under focus. *)
val no_focused_goal : proof -> bool

(*** Tactics ***)

val run_tactic : Environ.env -> unit Proofview.tactic -> proof -> proof

val emit_side_effects : Declareops.side_effects -> proof -> proof

val maximal_unfocus : 'a focus_kind -> proof -> proof

(*** Commands ***)

val in_proof : proof -> (Evd.evar_map -> 'a) -> 'a

(*** Compatibility layer with <=v8.2 ***)
module V82 : sig
  val subgoals : proof -> Goal.goal list Evd.sigma

  (* All the subgoals of the proof, including those which are not focused. *)
  val background_subgoals : proof -> Goal.goal list Evd.sigma

  val top_goal : proof -> Goal.goal Evd.sigma

  (* returns the existential variable used to start the proof *)
  val top_evars : proof -> Evd.evar list

  (* Turns the unresolved evars into goals.
     Raises [UnfinishedProof] if there are still unsolved goals. *)
  val grab_evars : proof -> proof

  (* Implements the Existential command *)
  val instantiate_evar : int -> Constrexpr.constr_expr -> proof -> proof
end
