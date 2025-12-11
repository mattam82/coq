type t = {
  sort_polymorphic : bool;
  level_polymorphic : bool;
  cumulative : bool }

let make ~level_polymorphic ~sort_polymorphic ~cumulative =
  if (sort_polymorphic || cumulative) && not level_polymorphic then
    CErrors.user_err Pp.(str "Cannot have sort polymorphic or cumulative but not level polymorphic constructions");
  { sort_polymorphic; level_polymorphic; cumulative }

let default = { sort_polymorphic = false; level_polymorphic = false; cumulative = false }
let of_poly b = { default with level_polymorphic = b }

let sort_polymorphic x = x.sort_polymorphic
let level_polymorphic x = x.level_polymorphic
let cumulative x = x.cumulative

let is_polymorphic = level_polymorphic

(* Used to have distinguished default behaviors when treating assumptions/axioms vs definitions *)
type assumption_or_definition =
  Assumption | Definition
