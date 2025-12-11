type t
(* Set of flags for sort polymorphism, universe level polymorphism and cumulativity *)

(* Raises an error if sort_poly or cumulative is true but poly isn't *)
val make : level_polymorphic:bool -> sort_polymorphic:bool -> cumulative:bool -> t

(* All false *)
val default : t

(* Only set the universe polymorphism flag *)
val of_poly : bool -> t

val sort_polymorphic : t -> bool
val level_polymorphic : t -> bool
val cumulative : t -> bool

(* Alias of level_polymorphic *)
val is_polymorphic : t -> bool

(* Used to have distinguished default behaviors when treating assumptions/axioms vs definitions *)
type assumption_or_definition =
  Assumption | Definition
