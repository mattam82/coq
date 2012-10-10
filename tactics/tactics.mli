(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Term
open Context
open Environ
open Tacmach
open Proof_type
open Reduction
open Evd
open Evar_refiner
open Clenv
open Redexpr
open Tacticals
open Globnames
open Genarg
open Tacexpr
open Nametab
open Glob_term
open Pattern
open Termops
open Unification
open Misctypes
open Locus

(** Main tactics. *)

(** {6 General functions. } *)

val string_of_inductive : constr -> string
val head_constr       : constr -> constr
val head_constr_bound : constr -> constr
val is_quantified_hypothesis : Id.t -> goal sigma -> bool

exception Bound

(** {6 Primitive tactics. } *)

val introduction    : Id.t -> tactic
val refine          : constr -> tactic
val convert_concl   : constr -> cast_kind -> tactic
val convert_hyp     : named_declaration -> tactic
val thin            : Id.t list -> tactic
val mutual_fix      :
  Id.t -> int -> (Id.t * int * constr) list -> int -> tactic
val fix             : Id.t option -> int -> tactic
val mutual_cofix    : Id.t -> (Id.t * constr) list -> int -> tactic
val cofix           : Id.t option -> tactic

val convert         : constr -> constr -> tactic
val convert_leq     : constr -> constr -> tactic

(** {6 Introduction tactics. } *)

val fresh_id_in_env : Id.t list -> Id.t -> env -> Id.t
val fresh_id : Id.t list -> Id.t -> goal sigma -> Id.t
val find_intro_names : rel_context -> goal sigma -> Id.t list

val intro                : tactic
val introf               : tactic
val intro_move        : Id.t option -> Id.t move_location -> tactic

  (** [intro_avoiding idl] acts as intro but prevents the new Id.t
     to belong to [idl] *)
val intro_avoiding       : Id.t list -> tactic

val intro_replacing      : Id.t -> tactic
val intro_using          : Id.t -> tactic
val intro_mustbe_force   : Id.t -> tactic
val intro_then           : (Id.t -> tactic) -> tactic
val intros_using         : Id.t list -> tactic
val intro_erasing        : Id.t -> tactic
val intros_replacing     : Id.t list -> tactic

val intros               : tactic

(** [depth_of_quantified_hypothesis b h g] returns the index of [h] in
   the conclusion of goal [g], up to head-reduction if [b] is [true] *)
val depth_of_quantified_hypothesis :
  bool -> quantified_hypothesis -> goal sigma -> int

val intros_until_n_wored : int -> tactic
val intros_until         : quantified_hypothesis -> tactic

val intros_clearing      : bool list -> tactic

(** Assuming a tactic [tac] depending on an hypothesis identifier,
   [try_intros_until tac arg] first assumes that arg denotes a
   quantified hypothesis (denoted by name or by index) and try to
   introduce it in context before to apply [tac], otherwise assume the
   hypothesis is already in context and directly apply [tac] *)

val try_intros_until :
  (Id.t -> tactic) -> quantified_hypothesis -> tactic

(** Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

val onInductionArg :
  (constr with_bindings -> tactic) ->
    constr with_bindings induction_arg -> tactic

(** Complete intro_patterns up to some length; fails if more patterns
   than required *)

val adjust_intro_patterns : int -> intro_pattern_expr located list ->
  intro_pattern_expr located list

(** {6 Introduction tactics with eliminations. } *)

val intro_pattern  : Id.t move_location -> intro_pattern_expr -> tactic
val intro_patterns : intro_pattern_expr located list -> tactic
val intros_pattern :
  Id.t move_location -> intro_pattern_expr located list -> tactic

(** {6 Exact tactics. } *)

val assumption       : tactic
val exact_no_check   : constr -> tactic
val vm_cast_no_check : constr -> tactic
val exact_check      : constr -> tactic
val exact_proof      : Constrexpr.constr_expr -> tactic

(** {6 Reduction tactics. } *)

type tactic_reduction = env -> evar_map -> constr -> constr

val reduct_in_hyp     : tactic_reduction -> hyp_location -> tactic
val reduct_option     : tactic_reduction * cast_kind -> goal_location -> tactic
val reduct_in_concl   : tactic_reduction * cast_kind -> tactic
val change_in_concl   : (occurrences * constr_pattern) option -> constr -> 
                        tactic
val change_in_hyp     : (occurrences * constr_pattern) option -> constr ->
                        hyp_location -> tactic
val red_in_concl      : tactic
val red_in_hyp        : hyp_location -> tactic
val red_option        : goal_location -> tactic
val hnf_in_concl      : tactic
val hnf_in_hyp        : hyp_location -> tactic
val hnf_option        : goal_location -> tactic
val simpl_in_concl    : tactic
val simpl_in_hyp      : hyp_location -> tactic
val simpl_option      : goal_location -> tactic
val normalise_in_concl : tactic
val normalise_in_hyp  : hyp_location -> tactic
val normalise_option  : goal_location -> tactic
val normalise_vm_in_concl : tactic
val unfold_in_concl   :
  (occurrences * evaluable_global_reference) list -> tactic
val unfold_in_hyp     :
  (occurrences * evaluable_global_reference) list -> hyp_location -> tactic
val unfold_option     :
  (occurrences * evaluable_global_reference) list -> goal_location -> tactic
val change            :
  constr_pattern option -> constr -> clause -> tactic
val pattern_option    :
  (occurrences * constr) list -> goal_location -> tactic
val reduce            : red_expr -> clause -> tactic
val unfold_constr     : global_reference -> tactic

(** {6 Modification of the local context. } *)

val clear         : Id.t list -> tactic
val clear_body    : Id.t list -> tactic
val keep          : Id.t list -> tactic
val clear_if_overwritten : constr -> intro_pattern_expr located list -> tactic

val specialize    : int option -> constr with_bindings -> tactic

val move_hyp      : bool -> Id.t -> Id.t move_location -> tactic
val rename_hyp    : (Id.t * Id.t) list -> tactic

val revert        : Id.t list -> tactic

(** {6 Resolution tactics. } *)

val apply_type : constr -> constr list -> tactic
val apply_term : constr -> constr list -> tactic
val bring_hyps : named_context -> tactic

val apply                 : constr -> tactic
val eapply                : constr -> tactic

val apply_with_bindings_gen :
  advanced_flag -> evars_flag -> constr with_bindings located list -> tactic

val apply_with_bindings   : constr with_bindings -> tactic
val eapply_with_bindings  : constr with_bindings -> tactic

val cut_and_apply         : constr -> tactic

val apply_in :
  advanced_flag -> evars_flag -> Id.t -> 
    constr with_bindings located list ->
    intro_pattern_expr located option -> tactic

val simple_apply_in : Id.t -> constr -> tactic

(** {6 Elimination tactics. } *)


(*
   The general form of an induction principle is the following:

   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional                optional
               even if HI      argument added if principle
             present above   generated by functional induction
             [indarg]          [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).
*)

(** [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = {
  elimc: constr with_bindings option;
  elimt: types;
  indref: global_reference option;
  index: int;              (** index of the elimination type in the scheme *)
  params: rel_context;     (** (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;            (** number of parameters *)
  predicates: rel_context; (** (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;        (** Number of predicates *)
  branches: rel_context;   (** branchr,...,branch1 *)
  nbranches: int;          (** Number of branches *)
  args: rel_context;       (** (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;              (** number of arguments *)
  indarg: rel_declaration option; (** Some (H,I prm1..prmp x1...xni)
				     if HI is in premisses, None otherwise *)
  concl: types;            (** Qi x1...xni HI (f...), HI and (f...)
			      are optional and mutually exclusive *)
  indarg_in_concl: bool;   (** true if HI appears at the end of conclusion *)
  farg_in_concl: bool;     (** true if (f...) appears at the end of conclusion *)
}


val compute_elim_sig : ?elimc: constr with_bindings -> types -> elim_scheme
val rebuild_elimtype_from_scheme: elim_scheme -> types

(** elim principle with the index of its inductive arg *)
type eliminator = {
  elimindex : int option;  (** None = find it automatically *)
  elimbody : constr with_bindings
}

val elimination_clause_scheme : evars_flag -> ?flags:unify_flags -> 
  int -> clausenv -> clausenv -> tactic

val elimination_in_clause_scheme : evars_flag -> ?flags:unify_flags -> 
  Id.t -> int -> clausenv -> clausenv -> tactic

val general_elim_clause_gen : (int -> Clenv.clausenv -> 'a -> tactic) ->
  'a -> eliminator -> tactic

val general_elim  : evars_flag ->
  constr with_bindings -> eliminator -> tactic
val general_elim_in : evars_flag -> Id.t ->
  constr with_bindings -> eliminator -> tactic

val default_elim  : evars_flag -> constr with_bindings -> tactic
val simplest_elim : constr -> tactic
val elim :
  evars_flag -> constr with_bindings -> constr with_bindings option -> tactic

val simple_induct : quantified_hypothesis -> tactic

val new_induct : evars_flag -> 
  (evar_map * constr with_bindings) induction_arg list ->
  constr with_bindings option ->
    intro_pattern_expr located option * intro_pattern_expr located option ->
      clause option -> tactic

(** {6 Case analysis tactics. } *)

val general_case_analysis : evars_flag -> constr with_bindings ->  tactic
val simplest_case         : constr -> tactic

val simple_destruct          : quantified_hypothesis -> tactic
val new_destruct : evars_flag ->
  (evar_map * constr with_bindings) induction_arg list ->
  constr with_bindings option ->
    intro_pattern_expr located option * intro_pattern_expr located option ->
      clause option -> tactic

(** {6 Generic case analysis / induction tactics. } *)

val induction_destruct : rec_flag -> evars_flag ->
  ((evar_map * constr with_bindings) induction_arg *
  (intro_pattern_expr located option * intro_pattern_expr located option))
  list *
  constr with_bindings option *
  clause option -> tactic

(** {6 Eliminations giving the type instead of the proof. } *)

val case_type         : constr  -> tactic
val elim_type         : constr  -> tactic

(** {6 Some eliminations which are frequently used. } *)

val impE : Id.t -> tactic
val andE : Id.t -> tactic
val orE  : Id.t -> tactic
val dImp : clause -> tactic
val dAnd : clause -> tactic
val dorE : bool -> clause ->tactic


(** {6 Introduction tactics. } *)

val constructor_tac      : evars_flag -> int option -> int ->
  constr bindings -> tactic
val any_constructor      : evars_flag -> tactic option -> tactic
val one_constructor      : int -> constr bindings  -> tactic

val left                 : constr bindings -> tactic
val right                : constr bindings -> tactic
val split                : constr bindings -> tactic

val left_with_bindings  : evars_flag -> constr bindings -> tactic
val right_with_bindings : evars_flag -> constr bindings -> tactic
val split_with_bindings : evars_flag -> constr bindings list -> tactic

val simplest_left        : tactic
val simplest_right       : tactic
val simplest_split       : tactic

(** {6 Logical connective tactics. } *)

val setoid_reflexivity          : tactic Hook.t
val reflexivity_red             : bool -> tactic
val reflexivity                 : tactic
val intros_reflexivity          : tactic

val setoid_symmetry             : tactic Hook.t
val symmetry_red                : bool -> tactic
val symmetry                    : tactic
val setoid_symmetry_in          : (Id.t -> tactic) Hook.t
val symmetry_in                 : Id.t -> tactic
val intros_symmetry             : clause -> tactic

val setoid_transitivity         : (constr option -> tactic) Hook.t
val transitivity_red            : bool -> constr option -> tactic
val transitivity                : constr -> tactic
val etransitivity               : tactic
val intros_transitivity         : constr option -> tactic

val cut                         : constr -> tactic
val cut_intro                   : constr -> tactic
val assert_replacing            : Id.t -> types -> tactic -> tactic
val cut_replacing               : Id.t -> types -> tactic -> tactic
val cut_in_parallel             : constr list -> tactic

val assert_as : bool -> intro_pattern_expr located option -> constr -> tactic
val forward   : tactic option -> intro_pattern_expr located option -> constr -> tactic
val letin_tac : (bool * intro_pattern_expr located) option -> Name.t ->
  constr -> types option -> clause -> tactic
val letin_pat_tac : (bool * intro_pattern_expr located) option -> Name.t ->
  evar_map * constr -> types option -> clause -> tactic
val assert_tac : Name.t -> types -> tactic
val assert_by  : Name.t -> types -> tactic -> tactic
val pose_proof : Name.t -> constr -> tactic

val generalize      : constr list -> tactic
val generalize_gen  : ((occurrences * constr) * Name.t) list -> tactic
val generalize_dep  : ?with_let:bool (** Don't lose let bindings *) -> constr  -> tactic

val unify           : ?state:Names.transparent_state -> constr -> constr -> tactic
val resolve_classes : tactic

val tclABSTRACT : Id.t option -> tactic -> tactic

val admit_as_an_axiom : tactic

val abstract_generalize : ?generalize_vars:bool -> ?force_dep:bool -> Id.t -> tactic
val specialize_eqs : Id.t -> tactic

val general_multi_rewrite :
  (bool -> evars_flag -> constr with_bindings -> clause -> tactic) Hook.t

val subst_one :
  (bool -> Id.t -> Id.t * constr * bool -> tactic) Hook.t


val declare_intro_decomp_eq :
  ((int -> tactic) -> Coqlib.coq_eq_data * types *
   (types * constr * constr) ->
   clausenv -> tactic) -> unit

val emit_side_effects : Declareops.side_effects -> tactic
