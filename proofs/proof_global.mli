(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines proof facilities relevant to the
     toplevel. In particular it defines the global proof
     environment. *)

(** Type of proof modes :
    - A name
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it 

*)
type proof_mode = {
  name : string ;
  set : unit -> unit ;
  reset : unit -> unit
}

(** Registers a new proof mode which can then be adressed by name
    in [set_default_proof_mode].
    One mode is already registered - the standard mode - named "No",
    It corresponds to Coq default setting are they are set when coqtop starts. *)
val register_proof_mode : proof_mode -> unit

val there_are_pending_proofs : unit -> bool
val check_no_pending_proof : unit -> unit

val get_current_proof_name : unit -> Names.Id.t
val get_all_proof_names : unit -> Names.Id.t list

val discard : Names.Id.t Loc.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

(** [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
val set_proof_mode : string -> unit

exception NoCurrentProof
val give_me_the_proof : unit -> Proof.proof
(** @raise NoCurrentProof when outside proof mode. *)

type proof_decl_hook = 
  (Universes.universe_opt_subst Univ.in_universe_context -> 
   Decl_kinds.locality -> Globnames.global_reference -> unit) option

(** [start_proof s str goals ~init_tac ~compute_guard hook] starts 
    a proof of name [s] and
    conclusion [t]; [hook] is optionally a function to be applied at
    proof end (e.g. to declare the built constructions as a coercion
    or a setoid morphism). *)
type lemma_possible_guards = int list list
val start_proof : Names.Id.t -> 
                          Decl_kinds.goal_kind ->
                          (Environ.env * Term.types Univ.in_universe_context_set) list  ->
                          ?compute_guard:lemma_possible_guards -> 
  proof_decl_hook -> unit

type closed_proof =
  Names.Id.t *
  (Entries.definition_entry list * lemma_possible_guards *
    Decl_kinds.goal_kind * unit Tacexpr.declaration_hook)

val close_proof : unit -> closed_proof

(* Intermediate step necessary to delegate the future.
 * Both access the current proof state. The formes is supposed to be
 * chained with a computation that completed the proof *)
val return_proof : fix_exn:(exn -> exn) -> Entries.proof_output list
val close_future_proof :
  Entries.proof_output list Future.computation -> closed_proof

exception NoSuchProof

val get_open_goals : unit -> int

(** Runs a tactic on the current proof. Raises [NoCurrentProof] is there is 
   no current proof. *)
val with_current_proof :
  (unit Proofview.tactic -> Proof.proof -> Proof.proof) -> unit

(** Sets the tactic to be used when a tactic line is closed with [...] *)
val set_endline_tactic : Tacexpr.raw_tactic_expr -> unit
val set_interp_tac :
  (Tacexpr.raw_tactic_expr -> Goal.goal Evd.sigma -> Goal.goal list Evd.sigma)
    -> unit

(** Sets the section variables assumed by the proof *)
val set_used_variables : Names.Id.t list -> unit
val get_used_variables : unit -> Context.section_context option

val discard : Names.identifier Loc.located -> unit
val discard_current : unit -> unit
val discard_all : unit -> unit

(**********************************************************)
(*                                                        *)
(*                            Proof modes                 *)
(*                                                        *)
(**********************************************************)


val activate_proof_mode : string -> unit
val disactivate_proof_mode : string -> unit

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet : sig
  type t = Vernacexpr.bullet

  (** A [behavior] is the data of a put function which
      is called when a bullet prefixes a tactic, together
      with a name to identify it. *)
  type behavior = {
    name : string;
    put : Proof.proof -> t -> Proof.proof
  }

  (** A registered behavior can then be accessed in Coq
      through the command [Set Bullet Behavior "name"].

      Two modes are registered originally:
      * "Strict Subproofs":
        - If this bullet follows another one of its kind, defocuses then focuses
          (which fails if the focused subproof is not complete).
        - If it is the first bullet of its kind, then focuses a new subproof.
      * "None": bullets don't do anything *)
  val register_behavior : behavior -> unit

  (** Handles focusing/defocusing with bullets:
       *)
  val put : Proof.proof -> t -> Proof.proof
end

module V82 : sig
  val get_current_initial_conclusions : unit -> Names.Id.t *
    (Term.types list * Decl_kinds.goal_kind *
     (proof_decl_hook))
end

type state
val freeze : marshallable:[`Yes | `No | `Shallow] -> state
val unfreeze : state -> unit
