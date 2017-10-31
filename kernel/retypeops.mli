(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constr
open Environ

(** {6 Retyping. }

   Re-infering the type of a term under the assumption that it is
   well typed.
 *)

val infer      : env -> evar_closures -> constr -> types
val infer_type : env -> evar_closures -> types  -> Sorts.t

(** We can take advantage of non-cumulativity of SProp to avoid fully
   retyping terms when we just want to know if they inhabit some
   proof-irrelevant type. *)
val is_irrelevant_term : env -> evar_closures -> constr -> bool
