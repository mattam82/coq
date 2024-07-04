(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Notations.
Require Import Types.Nat.

Inductive list@{s|u|} (A : Type@{s|u}) : Type@{s|u} :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

Declare Scope list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Infix "::" := cons (at level 60, right associativity) : list_scope.

Register list as core.list.type.
Register nil as core.list.nil.
Register cons as core.list.cons.

Section ListPolyDefinitions.
  Sort s.
  Universe u.
  Context {A : Type@{s|u}}.

  #[local] Open Scope list_scope.

  Fixpoint length (l : list A) : nat@{s|} :=
    match l with
    | nil => O
    | _ :: l' => S (length l')
    end.

(** Concatenation of two lists *)

  Fixpoint app (l1 l2 : list A) : list A :=
    match l1 with
    | nil => l2
    | a :: l1' => a :: app l1' l2
    end.

  Section Map.
    Universe u'.
    Context (B : Type@{s|u'})
            (f : A -> B).

    Fixpoint map (l : list A) : list B :=
      match l with
        | nil => nil
        | a :: t => (f a) :: (map t)
      end.

  End Map.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len : nat@{s|}) : list nat :=
    match len with
      | O => nil
      | S len => start :: seq (S start) len
    end.

  Fixpoint repeat (x : A) (n: nat@{s|}) :=
    match n with
      | O => nil
      | S k => x :: repeat x k
    end.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n : nat@{s|}) (l : list A) (default : A) {struct l} : A :=
    match n, l with
      | _, nil => default
      | O, x :: l' => x
      | S m, x :: t => nth m t default
    end.

  Fixpoint firstn (n : nat@{s|}) (l : list A) : list A :=
    match n with
      | O => nil
      | S n => match l with
                  | nil => nil
                  | a :: l => a :: (firstn n l)
                end
    end.

  Fixpoint skipn (n : nat@{s|}) (l : list A) : list A :=
    match n with
      | O => l
      | S n => match l with
                  | nil => nil
                  | a :: l => skipn n l
                end
    end.

  Inductive Forall (P : A -> Prop) : list A -> Prop :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall x l, P x -> Forall P l -> Forall P (x :: l).

End ListPolyDefinitions.

Infix "++" := app (right associativity, at level 60) : list_scope.
