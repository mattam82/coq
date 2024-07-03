(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Require Import PreludeOptions.
Require Import Notations.

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].
*)

(** listings: sigma def **)
Inductive sigma@{s s' s''|u v| } (A:Type@{s|u}) (P:A -> Type@{s'|v}) :
  Type@{s''|max(u,v)} :=
    existP : forall x:A, P x -> sigma A P.
(** listings: end **)

Arguments existP {_ _}.

Scheme sigma_poly := Induction for sigma Sort Poly.

Record sigmaR@{s|u v|} (A : Type@{s|u}) (P:A -> Type@{s|v}) : Type@{s|max(u,v)} := existR
  { fst : A ; snd : P fst }.

Arguments existR {_ _}.

Scheme sigmaR_poly := Induction for sigma Sort Poly.

Notation "A * B" := (sigmaR A (fun _ => B)).

Definition ex@{s|u|} {A:Type@{s|u}} (P:A -> Prop) : Prop := sigma@{_ _ _|_ Set} A P.

Notation "'ex_intro'" := (existP@{_ _ _| _ Set}) (at level 50).

Register ex as core.ex.type.
Register existP as core.ex.intro.

Section Projections.

  Context {A:Prop} {P:A->Prop}.

  Definition ex_proj1 (x:ex P) : A :=
    match x with ex_intro a _ => a end.

  Definition ex_proj2 (x:ex P) : P (ex_proj1 x) :=
    match x with ex_intro _ b => b end.

  Register ex_proj1 as core.ex.proj1.
  Register ex_proj2 as core.ex.proj2.

End Projections.

Notation "'Σ' x .. y , B" := (sigma _ (fun x => .. (sigma _ (fun y => B)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' B ']'")
  : type_scope.

Notation "( x , .. , y , z )" := (existP x .. (existP y z) ..).

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.


(** Subsets and Sigma-types *)

(** [(sig A P)], or more suggestively [{x:A | P x}], denotes the subset
    of elements of the type [A] which satisfy the predicate [P].
    Similarly [(sig2 A P Q)], or [{x:A | P x & Q x}], denotes the subset
    of elements of the type [A] which satisfy both [P] and [Q]. *)

Definition sig@{s|u|} {A:Type@{s|u}} (P:A -> Prop) : Type@{s|u} := sigma@{s Prop s| u Set} A P.
 
Notation exist := existP.
Definition sig_rect@{u u'} := sigma_poly@{Type SProp Type | u Set u'}.

Register sig as core.sig.type.

Register sig_rect as core.sig.rect.




(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Notation sigT := (@sigmaR _).
Notation existT := @existR.

Register sigmaR as core.sigT.type.
Register existR as core.sigT.intro.

Definition sigT_rect@{| u u' u''|} := sigmaR_poly@{Type Type Type|u u' u''}.

Register sigT_rect as core.sigT.rect.

Record sigT2@{s|u v|} {A:Type@{s|u}} (B C:A -> Type@{s|v}) : Type@{s|max(u,v)} := existT2
  { fst2 : A;
    snd2 : B fst2;
    thd2: C fst2}.


(* Notations *)

Arguments sig (A P)%_type.
Arguments sigmaR (A P)%_type.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x : A & P }" := (@sigT A (fun x => P)) : type_scope.

Notation "{ ' pat | P }" := (sig (fun pat => P)) : type_scope.
Notation "{ ' pat : A | P }" := (sig (A:=A) (fun pat => P)) : type_scope.
Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
Notation "{ ' pat : A & P }" := (@sigT A (fun pat => P)) : type_scope.

Add Printing Let sigma.

(** Projections of [sig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(proj1_sig y)] is the witness [a] and [(proj2_sig y)] is the
    proof of [(P a)] *)

(* Set Universe Polymorphism. *)
Register fst as core.sig.proj1.
Register snd as core.sig.proj2.



(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(projT1 x)] is the first projection and [(projT2 x)] is the
    second projection, the type of which depends on the [projT1]. *)

Register fst as core.sigT.proj1.
Register snd as core.sigT.proj2.

Module SigTNotations.
  Notation "( x ; y )" := (existT _ x y) (at level 0, format "( x ;  '/  ' y )").
  Notation "x .1" := (fst x) (at level 1, left associativity, format "x .1").
  Notation "x .2" := (snd x) (at level 1, left associativity, format "x .2").
End SigTNotations.

Import SigTNotations.
