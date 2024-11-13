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

(* Set Cumulative Prop. *)

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].
*)

(** listings: sigma **)
Inductive sigma@{s s' s''|u v| } (A:Type@{s|u}) (P:A -> Type@{s'|v}) : Type@{s''|max(u,v)}
  :=  exist : forall x:A, P x -> sigma A P.
(** listings: end **)

Arguments exist {_ _}.

(* Register ? *)

(** listings: proj1 **)
Definition proj1@{s s'|u v|} {A:Type@{s|u}} {P:A -> Type@{s'|v}}
  (p : sigma@{s s' s|_ _} A P) : A := match p with exist a _ => a end.
(** listings: end **)

Definition proj2@{s|u v|} {A:Type@{s|u}} {P:A -> Type@{s|v}} (p : sigma@{_ _ s|_ _} A P) : P (proj1 p) := match p with exist _ b => b end.

Definition π1@{s s'|u v|} {A:Type@{s|u}} {P:A -> Type@{s'|v}} (p : sigma@{_ _ Type|_ _} A P) : A :=
  match p return A with exist a _ => a end.

Definition π2@{s s'|u v|} {A:Type@{s|u}} {P:A -> Type@{s'|v}} (p : sigma@{_ _ Type|_ _} A P) : P (π1 p) := match p with exist _ b => b end.

Definition ex@{s|u|} {A:Type@{s|u}} (P:A -> Prop) : Prop := sigma@{s Prop Prop|u Set} A P.

Notation "'ex_intro'" := (exist@{_ Prop Prop| _ Set}) (at level 50).

Register ex as core.ex.type.
Register exist as core.ex.intro.

Section ProjectionsProp.

  Context {A:Prop} {P:A->Prop}.

  Definition ex_proj1 (x:ex P) : A :=
    match x with ex_intro a _ => a end.

  Definition ex_proj2 (x:ex P) : P (ex_proj1 x) :=
    match x with ex_intro _ b => b end.

  Register ex_proj1 as core.ex.proj1.
  Register ex_proj2 as core.ex.proj2.

End ProjectionsProp.

Notation "'Σ' x .. y , B" := (sigma _ (fun x => .. (sigma _ (fun y => B)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' B ']'")
  : type_scope.

Notation "( x , .. , y , z )" := (exist x .. (exist y z) ..).

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
 
Definition sig_rect@{u u'} := sigma_elim@{Type SProp Type | u Set u'}.

Register sigma as core.sig.type.

Register sig_rect as core.sig.rect.
Notation proj1_sig := proj1.
Notation proj2_sig := proj2.

(** listings: sigmaR **)
Record sigmaR@{s|u v|} (A : Type@{s|u}) (P:A -> Type@{s|v}) : Type@{s|max(u,v)}
  := existR { fst : A ; snd : P fst }.
(** listings: end **)

Arguments fst {_ _}.
Arguments snd {_ _}.
Arguments existR {_ _}.

Notation "( x ; .. ; y ; z )" := (existR x .. (existR y z) ..).

Scheme sigmaR_elim := Induction for sigmaR Sort Poly.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Section Prod.
  Sort s.
  Universe u v.
  Context {A : Type@{s|u}} {B : Type@{s|v}}.
  Definition prod := sigmaR A (fun _ => B).
  Definition pair (a : A) (b : B) : prod := {| fst := a ; snd := b |}.
  Definition prod_rect@{o} (P : prod -> Type@{s|o}) (h : forall a b, P (pair a b)) : forall p, P p := fun p => h p.(fst) p.(snd).
End Prod.

Arguments prod : clear implicits.
Notation "A * B" := (prod A B).
Notation "A /\ B" := (prod@{Prop|_ _} A B).

Register prod as core.prod.type.
Register pair as core.prod.intro.
Register prod_rect as core.prod.rect.

Register fst as core.prod.proj1.
Register snd as core.prod.proj2.

#[global]
Hint Resolve pair : core.




(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Notation sigT := (@sigmaR _).
Notation existT := @existR.

Register sigmaR as core.sigT.type.
Register existR as core.sigT.intro.

Definition sigT_rect@{| u u' u''|} := sigmaR_elim@{Type|u u' u''}.

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
Notation "{ x : A & P }" := (@sigmaR A (fun x => P)) : type_scope.

Notation "{ ' pat | P }" := (sig (fun pat => P)) : type_scope.
Notation "{ ' pat : A | P }" := (sig (A:=A) (fun pat => P)) : type_scope.
Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
Notation "{ ' pat : A & P }" := (@sigmaR A (fun pat => P)) : type_scope.

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
    [(proj1 x)] is the first projection and [(projT2 x)] is the
    second projection, the type of which depends on the [proj1]. *)

Register fst as core.sigT.proj1.
Register snd as core.sigT.proj2.

Module SigTNotations.
  Notation "( x ; y )" := (existT _ x y) (at level 0, format "( x ;  '/  ' y )").
  Notation "x .1" := (fst x) (at level 1, left associativity, format "x .1").
  Notation "x .2" := (snd x) (at level 1, left associativity, format "x .2").
End SigTNotations.

Import SigTNotations.
