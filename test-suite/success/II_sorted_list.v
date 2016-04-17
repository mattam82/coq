Require Import Coq.Structures.Orders.

Unset Elimination Schemes.

(** Sorted lists *)

Module SortedLists (Import A : OrderedType).

  Inductive SList : Type :=
  | slist_nil  : SList
  | slist_cons : forall (x : t) (ys : SList), slist_lt x ys -> SList
  with slist_lt : t -> SList -> Type :=
  | slist_lt_triv (x : t) : slist_lt x slist_nil
  | slist_lt_cons (x' x : t) (ys : SList) (p : slist_lt x ys)
    : lt x' x -> slist_lt x' ys -> slist_lt x' (slist_cons x ys p)
  .

  (* Simple elimination schemes, not dependent enough *)
  Scheme slist_elim := Induction for SList Sort Type
  with slist_lt_elim := Induction for slist_lt Sort Type.

  Print slist_elim.

End SortedLists.
