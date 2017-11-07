(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Syntactic comparison between terms upto cumulativity of inductive types *)

open Constr

type conv_pb = CONV | CUMUL

val convert_inductives_gen : (Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a) ->
  (Univ.Constraint.t -> 'a -> 'a) ->
  conv_pb -> Declarations.mutual_inductive_body * int -> Int.t ->
  Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a

val convert_constructors_gen : (Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a) ->
  (Univ.Constraint.t -> 'a -> 'a) ->
  Declarations.mutual_inductive_body * int * int -> Int.t ->
  Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a

(* In the following functions we take the universe graph separate from
   the environment to allow to pass an extended graph (e.g. from an
   evar map). *)

(** [eq_constr_univs env univs a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [univs]. *)
val eq_constr_univs : Environ.env -> UGraph.t -> constr -> constr -> bool

(** [leq_constr_univs env univs a b] is [true] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe inequalities in [univs]. *)
val leq_constr_univs : Environ.env -> UGraph.t -> constr -> constr -> bool

(** [eq_constr_univs_infer env univs a b] is [Some c] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [univs] and [c]. *)
val eq_constr_univs_infer : Environ.env -> UGraph.t -> constr -> constr -> Univ.Constraint.t option

(** [leq_constr_univs_infer env univs a b] is [Some c] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe inequalities in [univs] and [c]. *)
val leq_constr_univs_infer : Environ.env -> UGraph.t -> constr -> constr -> Univ.Constraint.t option
