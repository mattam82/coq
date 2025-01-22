(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Notations.
Require Import Typeclasses.
Require Import Empty.


Class Has_refl@{sa se|la le|} (eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}) := refl : forall A x, eq A x x.

Arguments refl {_ _}.

Register Has_refl as rocq.core.Has_refl.


Class Has_J@{sa se sp|la le lp|} (eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}) (Has_refl : Has_refl eq) :=
  J : forall (A : Type@{sa | la}) (x : A) (P : forall y : A, eq A x y -> Type@{sp | lp}), P x (refl A x) -> forall y e, P y e.

Arguments J {_ _ _}.

Register Has_J as rocq.core.Has_J.

Class Has_Leibniz@{sa se sp|la le lp|} (eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}) :=
  leibniz : forall (A : Type@{sa | la}) (x : A) (P : A -> Type@{sp | lp}), P x -> forall y, eq A x y -> P y.

Class Has_Leibniz_r@{sa se sp|la le lp|} (eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}) :=
  leibniz_r : forall (A : Type@{sa | la}) (x : A) (P : A -> Type@{sp | lp}), P x -> forall y, eq A y x -> P y.

Arguments leibniz _ {_}.

Register Has_Leibniz as rocq.core.Has_Leibniz.
Register Has_Leibniz_r as rocq.core.Has_Leibniz_r.

Definition J_no_dep@{s s' sp|l l' lp|} {eq} {refl} (eqr : Has_J@{s s' sp|l l' lp} eq refl) :
  forall (A : Type@{s | l}) (x : A) (P : A -> Type@{sp | lp}), P x -> forall y (e : eq A x y), P y :=
  fun A x P px y e => J _ x (fun y _ => P y) px y e.

Definition Has_J_Has_Leibniz@{s s' sp|l l' lp|} {eq} {refl} (eqr : Has_J@{s s' sp|l l' lp} eq refl) : Has_Leibniz@{s s' sp|l l' lp} eq :=
  fun A x P px y e => J_no_dep _ A x P px y e.

#[projections(primitive=no)]
Class Has_JRefl@{sa se se' se''|la le le' le''|}
  (eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le})
  (Has_refl : Has_refl@{sa se|la le} eq)
  (Has_J : Has_J@{sa se se'|la le le'} eq Has_refl)
  (Has_Leibniz : Has_Leibniz@{sa se se'|la le le'} eq)
  (eqe : forall A : Type@{se' | le'}, A -> A -> Type@{se''|le''}) : Type
  :=
  {
    J_refl : forall (A : Type@{sa | la}) (x : A) (P : forall y : A, eq A x y -> Type@{se' | le'}) (f : P x (refl A x)), eqe _ (J A x P f x (refl A x)) f ;
    leibniz_refl : forall (A : Type@{sa | la}) (x : A) (P : A -> Type@{se' | le'}) (f : P x), eqe _ (leibniz eq A x P f x (refl A x)) f
  }.

Register Has_JRefl as rocq.core.Has_JRefl.

(** listings: eq **)
Inductive eq@{s s'|l|} {A:Type@{s|l}} (x:A) : A -> Type@{s'|l} :=
    eq_refl : eq x x.
(** listings: end **)
Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Notation "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (eq@{_ Prop|_} x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

(* Specialization of equality to a single sort *)
Definition eqdiag@{s|l|} {A : Type@{s|l}} := eq@{s s| l} (A:=A).

Notation "x ≡ y" := (eqdiag x y) (at level 60) : type_scope.
Notation "x ≡ y :> A" := (@eqdiag A x y) (at level 60) : type_scope.

Instance eq_Has_refl@{s s'|l|} : Has_refl@{s s'|l l} (@eq) :=
  fun A x => eq_refl.

Instance eq_Has_J_elim@{s se|l l'|} : Has_J@{s se se|l l l'} (@eq) _ := @eq_elim@{s se|l l'}.

Instance eq_Has_Leibniz_elim@{s se|l l'|} : Has_Leibniz@{s se se|l l l'} (@eq) :=
  fun A x P => @eq_elim@{s se|l l'} A x (fun y _ => P y).

Definition eq_ind@{s | u|} [A] [x] P := @eq_elim@{s Prop|u Set} A x (fun a _ => P a).

Definition eq_singleton@{s s' | u v|} [A:Type@{s|u}] [x:A]
  (P : forall a : A, x = a -> Type@{s'|v}) :
  P x (eq_refl x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Instance eq_Has_J_Singleton@{s sp|l lp} : Has_J@{s Prop sp|l 0 lp} (@eq) _ := @eq_singleton@{s sp|l lp}.

Instance eq_Has_Leibniz_Singleton@{s sp|l lp} : Has_Leibniz@{s Prop sp|l 0 lp} (@eq) :=
  fun A x P => @eq_singleton@{s sp|l lp} A x (fun y _ => P y).

Definition eq_rect@{u v} [A:Type@{u}] [x:A]
  (P : forall a : A, Type@{v}) :
  P x -> forall [a : A] (e : x = a), P a := @eq_singleton A x (fun a _ => P a).
(* this one generates additional universes  J@{Type Prop Type | _ 0 v} A x (fun a _ => P a) *)

Definition eq_rec@{u} [A:Type@{u}] [x:A]
  (P : forall a : A, Set) :
  P x -> forall [a : A] (e : x = a), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_sind [A:Set] [x:A]
  (P : forall a : A, SProp) :
  P x -> forall [a : A] (e : x = a), P a := @eq_singleton A x (fun a _ => P a).

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_sind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Instance eq_Has_J_Singleton_refl@{s sp|l lp|} : Has_JRefl@{s Prop sp Prop|l 0 lp 0} (@eq) _
  (eq_Has_J_Singleton@{s sp|l lp}) (eq_Has_Leibniz_Singleton@{s sp|l lp}) (@eq) :=
 { J_refl A x P f := eq_refl; leibniz_refl A x P f := eq_refl }.

Definition eq_type_elim@{s s' | u v|} [A:Type@{s|u}] [x:A]
  (P : forall a : A, (x = a :> A : Type@{u}) -> Type@{s'|v}) :
  P x (eq_refl x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Instance eq_Has_JType @{s sp|l lp|} : Has_J@{s Type sp|l l lp} (@eq@{s Type|l}) _ :=
  fun A x P Px y e => @eq_type_elim@{s sp|l lp} A x P Px y e.

Instance eq_Has_LeibnizType @{s sp|l lp|} : Has_Leibniz@{s Type sp|l l lp} (@eq@{s Type|l}) :=
  fun A x P Px y e => @eq_type_elim@{s sp|l lp} A x (fun y _ => P y) Px y e.

Instance eq_Has_J_Type_refl@{s sp|l lp|} : Has_JRefl@{s Prop sp Prop|l 0 lp 0} (@eq) _
  (eq_Has_J_Singleton@{s sp|l lp}) (eq_Has_Leibniz_Singleton@{s sp|l lp}) (@eq) :=
{ J_refl A x P f := eq_refl ; leibniz_refl A x P f := eq_refl }.

#[global]
Hint Resolve eq_refl: core.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.
Register eq_elim as core.eq.rect.

Section ap.
  Sort sa se sb se'.
  Universe la le lb le'.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {A : Type@{sa|la}}
          {eq' : forall A : Type@{sb | lb}, A -> A -> Type@{se'|le'}}
          {_refl: Has_refl@{sb se'|lb le'} eq'}
          {_leibniz: Has_Leibniz@{sa se se'|la le le'} eq}.

  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq _ x y) : type_scope.
  #[warnings="-notation-overridden"]
  Local Notation "x <> y" := (~ (eq _ x y)) : type_scope.

  Definition ap {B} (f : A -> B) {x y : A} (e : x = y) : eq' _ (f x) (f y) :=
    leibniz _ _ _ (fun y => eq' B (f x) (f y)) (refl _ _) _ e.

End ap.

Register ap as core.eq.congr.

Section apd.
  Sort sa sb se se'.
  Universe la le lb le'.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}
          {eq' : forall A : Type@{lb+1}, A -> A -> Type@{se'|le'}}
          {_refl': Has_refl@{Type se'|lb+1 le'} eq'}
          {_J: Has_J@{sa se se'|la le le'} eq _refl}.

  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq _ x y) : type_scope.
  #[warnings="-notation-overridden"]
  Local Notation "x <> y" := (~ (eq _ x y)) : type_scope.

  Definition apd {a} (P : forall b : A, a = b -> Type@{sb | lb})
    (b : A) (e : a = b) : eq' _ (P a (refl A a)) (P b e) :=
    J _ a (fun b e => eq' _ (P a (refl _ _)) (P b e)) (refl _ _) b e.

End apd.
