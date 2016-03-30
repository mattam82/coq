(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)

module LevelName :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val set : t
  val prop : t
  (** The set and prop universe levels. *)

  val is_small : t -> bool
  (** Is the universe set or prop? *)
		       
  val is_prop : t -> bool
  val is_set : t -> bool
  (** Is it specifically Prop or Set *)
		       
  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int

  val make : Names.DirPath.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val to_string : t -> string
  (** Debug printing *)

  val var : int -> t

  val var_index : t -> int option
end

module Level :
sig
  type t = LevelName.t * int
  (** Type of universe level expressions: 
      a level with a natural increment *)

  val make : LevelName.t -> t
  (** [make l] makes the level [l+0] *)

  val set : t
  val prop : t
  (** The set and prop universe levels. *)

  val succ : t -> t
  (** The successor universe *)
               
  val name : t -> LevelName.t
  (** Name of the level *)

  val is_small : t -> bool
  (** Is the universe set or prop? *)
		       
  val is_prop : t -> bool
  val is_set : t -> bool
  (** Is it specifically Prop or Set *)
		       
  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val hash : t -> int
  (** Hash function (constant time) *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val pr_with : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  (** Parameterized pretty-printing *)
  
  val to_string : t -> string
  (** Debug printing *)
end
  
type universe_level_name = LevelName.t
type universe_level = Level.t
(** Alias name. *)

(** Sets of universe levels *)
module LSet : 
sig 
  include CSig.SetS with type elt = universe_level_name
	      
  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  (** Pretty-printing *)
end

type universe_set = LSet.t

module Universe :
sig
  type t
  (** Type of universes. A universe is defined as a set of level expressions.
      A level expression is built from levels and successors of level expressions, i.e.:
      le ::= l + n, n \in N.

      A universe is said atomic if it consists of a single level expression with
      no increment, and algebraic otherwise (think the least upper bound of a set of
      level expressions).
  *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function on formal universes *)

  val hash : t -> int
  (** Hash function *)

  val make : Level.t -> t
  (** Create a universe representing the given level. *)

  val make_name : LevelName.t -> t
  (** Create a universe representing the given level. *)

  val pr : t -> Pp.std_ppcmds
  (** Pretty-printing *)

  val pr_with : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

  val is_level : t -> bool
  (** Test if the universe is a level or an algebraic universe. *)

  val var_index : t -> int option
                       
  val is_levels : t -> bool
  (** Test if the universe is a lub of levels or contains +n's. *)

  val level : t -> Level.t option
  (** Try to get a level out of a universe, returns [None] if it
      is an algebraic universe. *)

  val level_name : t -> LevelName.t option
  (** Try to get a level name out of a universe, returns [None] if it
      is an algebraic universe. *)

  val level_set : t -> LSet.t
  (** Get the level names inside the universe *)

  val levels : t -> Level.t list
  (** Deconstruct the universe as the l.u.b of levels *)
                           
  val addn : int -> t -> t
  (** Increment by n. n should be positive  *)

  val super : t -> t
  (** The universe strictly above *)
    
  val sup   : t -> t -> t
  (** The l.u.b. of 2 universes *)

  val type0m : t  
  (** image of Prop in the universes hierarchy *)
  
  val type0 : t  
  (** image of Set in the universes hierarchy *)
  
  val type1 : t 
  (** the universe of the type of Prop/Set *)

  val is_type0m : t -> bool
  val is_type0 : t -> bool
  (** Test for Prop = Type(0⁻) and Set = Type(0) *)
                
  val exists : (Level.t -> bool) -> t -> bool
  val for_all : (Level.t -> bool) -> t -> bool

end

type universe = Universe.t

(** Alias name. *)

val pr_uni : universe -> Pp.std_ppcmds
	      
(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ... 
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)
val type0m_univ : universe
val type0_univ : universe
val type1_univ : universe

val is_type0_univ : universe -> bool
val is_type0m_univ : universe -> bool
val is_univ_variable : universe -> bool
val is_small_univ : universe -> bool

val sup : universe -> universe -> universe
val super : universe -> universe

val universe_level : universe -> universe_level option

(** [univ_level_mem l u] Is l is mentionned in u ? *)

val univ_level_mem : universe_level -> universe -> bool

(** [univ_level_rem u v min] removes [u] from [v], resulting in [min]
    if [v] was exactly [u]. *)

val univ_level_rem : universe_level -> universe -> universe -> universe

(** {6 Support for universe polymorphism } *)

(** Polymorphic maps from universe levels to 'a *)
module LMap : 
sig
  include CMap.ExtS with type key = universe_level_name and module Set := LSet

  val union : 'a t -> 'a t -> 'a t
  (** [union x y] favors the bindings in the first map. *)

  val diff : 'a t -> 'a t -> 'a t
  (** [diff x y] removes bindings from x that appear in y (whatever the value). *)

  val subst_union : 'a option t -> 'a option t -> 'a option t
  (** [subst_union x y] favors the bindings of the first map that are [Some],
      otherwise takes y's bindings. *)

  val pr : ('a -> Pp.std_ppcmds) -> 'a t -> Pp.std_ppcmds
  (** Pretty-printing *)
end

type 'a universe_map = 'a LMap.t

(** {6 Substitution} *)

type universe_subst_fn = universe_level_name -> universe
type universe_level_subst_fn = universe_level_name -> universe_level_name

(** A full substitution, might involve algebraic universes *)
type universe_subst = universe universe_map
type universe_level_subst = universe_level_name universe_map

(** {6 Universe instances} *)

module Instance : 
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val of_array : Universe.t array -> t
  val to_array : t -> Universe.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val level_subst_fn : universe_level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val subst_fn : universe_subst_fn -> t -> t
  (** Substitution by a level-to-universe function. *)

  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  (** Pretty-printing, no comments *)

  val levels : t -> LSet.t
  (** The set of levels in the instance *)

  val map : (Universe.t -> Universe.t) -> t -> t
end

type universe_instance = Instance.t

(* Universe abstraction structure for contexts *)                           
module Abstraction : 
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val of_array : LevelName.t array -> t
  val to_array : t -> LevelName.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val subst_fn : universe_level_subst_fn -> t -> t
  (** Substitution by a level-to-level function. *)

  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds
  (** Pretty-printing, no comments *)

  val levels : t -> LSet.t
  (** The set of levels in the instance *)

  val instance : t -> Instance.t
  (** The abstraction seen as an instance. Use with caution,
      the level names in the abstraction are free. *)
end

type 'a puniverses = 'a * universe_instance
val out_punivs : 'a puniverses -> 'a
val in_punivs : 'a -> 'a puniverses

val eq_puniverses : ('a -> 'a -> bool) -> 'a puniverses -> 'a puniverses -> bool


(** {6 Constraints. } *)

type constraint_type = Lt | Le | Eq
type 'a univ_constraint = 'a * constraint_type * 'a

module Constraint : sig
  type t

  (** Set operations *)
  val empty : t
  val is_empty : t -> bool
  val union : t -> t -> t
  val diff : t -> t -> t
  val fold : (Level.t univ_constraint -> 'a -> 'a) -> t -> 'a -> 'a
  val equal : t -> t -> bool
  val for_all : (Level.t univ_constraint -> bool) -> t -> bool
  val pr : (LevelName.t -> Pp.std_ppcmds) -> t -> Pp.std_ppcmds

  (** {5 Enforcement of constraints}
    These smart constructors
    perform simplifications to avoid carrying trivial constraints. *)
  type 'a constraint_function = 'a -> 'a -> t -> t

  (** For universes, the translation to atomic constraints is the following:
  - max u v < w = u < w /\ v < w
  - w < max u v = w < u /\ v < w (* This is incomplete *)
  - max us = max vs = us <= vs /\ vs <= us (* This too is incomplete *)

  On the contrary, checking of these constraints is complete 
  (see check functions)
   *)
  val enforce : Universe.t univ_constraint -> t -> t
  val enforce_eq : universe constraint_function
  val enforce_leq : universe constraint_function

  (** For levels, any constraint l+n O k+m can be handled completely. *)
  val enforce_eq_level : universe_level constraint_function
  val enforce_leq_level : universe_level constraint_function
  val enforce_eq_instances : universe_instance constraint_function
  val add : Level.t univ_constraint -> t -> t
    
  (** Hashconsing *)
  val hcons_constraint : Level.t univ_constraint -> Level.t univ_constraint
  val hcons : t -> t
end

type constraints = Constraint.t

val empty_constraint : constraints
val union_constraint : constraints -> constraints -> constraints
val eq_constraint : constraints -> constraints -> bool

val enforce_eq : universe Constraint.constraint_function
[@@ deprecated]
val enforce_leq : universe Constraint.constraint_function
[@@ deprecated]
val enforce_eq_level : universe_level Constraint.constraint_function
[@@ deprecated]
val enforce_leq_level : universe_level Constraint.constraint_function
[@@ deprecated]
val enforce_eq_instances : universe_instance Constraint.constraint_function
[@@ deprecated]

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

(** Constrained *)
val constraints_of : 'a constrained -> constraints

(** Enforcing constraints. *)

(** Type explanation is used to decorate error messages to provide
  useful explanation why a given constraint is rejected. It is composed
  of a path of universes and relation kinds [(r1,u1);..;(rn,un)] means
   .. <(r1) u1 <(r2) ... <(rn) un (where <(ri) is the relation symbol
  denoted by ri, currently only < and <=). The lowest end of the chain
  is supposed known (see UniverseInconsistency exn). The upper end may
  differ from the second univ of UniverseInconsistency because all
  universes in the path are canonical. Note that each step does not
  necessarily correspond to an actual constraint, but reflect how the
  system stores the graph and may result from combination of several
  constraints...
*)
type explanation = (constraint_type * universe) list
type univ_inconsistency = constraint_type * universe * universe * explanation option

exception UniverseInconsistency of univ_inconsistency
                                                                     
(** A vector of universe levels with universe constraints,
    representiong local universe variables and associated constraints *)

module UContext :
sig 
  type t

  val make : Abstraction.t constrained -> t

  val empty : t
  val is_empty : t -> bool
    
  val abstraction : t -> Abstraction.t
  val constraints : t -> constraints

  val dest : t -> Abstraction.t * constraints

  (** Keeps the order of the instances *)
  val union : t -> t -> t

  (* the number of universes in the context *)
  val size : t -> int

  (* Make a dummy instance from the abstraction: 
     use with caution as the universes are not declared. *)
  val instance : t -> Instance.t
                   
end

type universe_context = UContext.t

(** Universe contexts (as sets) *)

module ContextSet :
sig 
  type t = universe_set constrained

  val empty : t
  val is_empty : t -> bool

  val singleton : universe_level_name -> t
  val of_abstraction : Abstraction.t -> t
  val of_set : universe_set -> t

  val equal : t -> t -> bool
  val union : t -> t -> t

  val append : t -> t -> t
  (** Variant of {!union} which is more efficient when the left argument is
      much smaller than the right one. *)

  val diff : t -> t -> t
  val add_universe : universe_level_name -> t -> t
  val add_constraints : constraints -> t -> t
  val add_abstraction : Abstraction.t -> t -> t

  (** Arbitrary choice of linear order of the variables *)
  val to_context : t -> universe_context
  val of_context : universe_context -> t

  val constraints : t -> constraints
  val levels : t -> universe_set
end

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)
type universe_context_set = ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

val empty_level_subst : universe_level_subst
val is_empty_level_subst : universe_level_subst -> bool

(** Substitution of universes. *)
val subst_univs_level_level_name : universe_level_subst -> universe_level_name -> universe_level_name
val subst_univs_level_level : universe_level_subst -> universe_level -> universe_level
val subst_univs_level_universe : universe_level_subst -> universe -> universe
val subst_univs_level_constraints : universe_level_subst -> constraints -> constraints
val subst_univs_level_abstraction : universe_level_subst -> Abstraction.t ->
                                    Abstraction.t
val subst_univs_level_instance : universe_level_subst -> universe_instance ->
                                 universe_instance

(** Level to universe substitutions. *)

val empty_subst : universe_subst
val is_empty_subst : universe_subst -> bool
val make_subst : universe_subst -> universe_subst_fn

val subst_univs_universe : universe_subst_fn -> universe -> universe
val subst_univs_constraints : universe_subst_fn -> constraints -> constraints

(** Substitution of instances *)
(* val subst_instance_instance : universe_instance -> universe_instance -> universe_instance *)
val subst_instance_universe : universe_instance -> universe -> universe
val subst_instance_constraints : universe_instance -> constraints -> constraints

val make_abstraction_subst : Abstraction.t -> universe_level_subst
val make_inverse_abstraction_subst : Abstraction.t -> universe_level_subst

val abstract_universes : bool -> universe_context -> universe_level_subst * universe_context

(** Get the instantiated graph. *)
val instantiate_univ_context : universe_context -> universe_context
val instantiate_univ_constraints : universe_instance -> universe_context -> constraints

(** {6 Pretty-printing of universes. } *)

val pr_constraint_type : constraint_type -> Pp.std_ppcmds
val pr_constraints : (LevelName.t -> Pp.std_ppcmds) -> constraints -> Pp.std_ppcmds
val pr_universe_context : (LevelName.t -> Pp.std_ppcmds) -> universe_context -> Pp.std_ppcmds
val pr_universe_context_set : (LevelName.t -> Pp.std_ppcmds) -> universe_context_set -> Pp.std_ppcmds
val explain_universe_inconsistency : (LevelName.t -> Pp.std_ppcmds) -> 
  univ_inconsistency -> Pp.std_ppcmds

val pr_universe_level_subst : universe_level_subst -> Pp.std_ppcmds
val pr_universe_subst : universe_subst -> Pp.std_ppcmds

(** {6 Hash-consing } *)

val hcons_univ : universe -> universe
val hcons_constraints : constraints -> constraints
val hcons_universe_set : universe_set -> universe_set
val hcons_universe_context : universe_context -> universe_context
val hcons_universe_context_set : universe_context_set -> universe_context_set 

(******)

(* deprecated: use qualified names instead *)
val compare_levels : universe_level_name -> universe_level_name -> int
val eq_levels : universe_level_name -> universe_level_name -> bool

(** deprecated: Equality of formal universe expressions. *)
val equal_universes : universe -> universe -> bool
