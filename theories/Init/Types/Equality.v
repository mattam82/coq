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
Require Import Empty.

Inductive eq@{s s'|l|} {A:Type@{s|l}} (x:A) : A -> Type@{s'|l} :=
    eq_refl : eq x x.
Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

(* Specialization of equality to a single sort *)
Definition eqdiag@{s|l|} {A : Type@{s|l}} := eq@{s s| l} (A:=A).

Notation "x ≡ y" := (eqdiag x y) (at level 60) : type_scope.
Notation "x ≡ y :> A" := (@eqdiag A x y) (at level 60) : type_scope.

Definition eq_ind@{s | u|} [A] [x] P := @eq_elim@{s Prop|u Set} A x (fun a _ => P a).

Definition eq_singleton@{s s' | u v|} [A:Type@{s|u}] [x:A]
  (P : forall a : A, (eq@{s Prop|u} x a) -> Type@{s'|v}) :
  P x (eq_refl x) -> forall [a : A] (e : x = a :> A), P a e :=
  fun t _ e => match e with eq_refl => t end.

Definition eq_rect@{u v|} [A:Type@{u}] [x:A]
  (P : forall a : A, Type@{v}) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_rec@{u|} [A:Type@{u}] [x:A]
  (P : forall a : A, Set) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Definition eq_sind [A:Set] [x:A]
  (P : forall a : A, SProp) :
  P x -> forall [a : A] (e : x = a :> A), P a := @eq_singleton A x (fun a _ => P a).

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_sind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Notation "x = y" := (eq@{_ Prop|_} x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve eq_refl: core.

Section GroupoidOperations.
  Sort sa se.
  Universe a.
  Context {A : Type@{sa|a}}.
  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq@{_ se|_} x y) : type_scope.

  Definition eq_sym {x y : A} (e : x = y) : y = x :=
    match e with | eq_refl _ => eq_refl _ end.

  Definition eq_trans {x y z : A} (e1 : x = y) : y = z -> x = z :=
    match e1 with | eq_refl _ => fun x => x end.

  Definition tr@{b|} {B : Type@{sa|b}} (e : @eq@{_ sa|max(a+1,b+1)} Type@{sa|max(a,b)} A B) : A -> B :=
    match e in @eq _ _ B return A -> B with | eq_refl _ => fun x => x end.

  Definition ap@{sb|b|} {B : Type@{sb|b}} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
    match e with | eq_refl _ => eq_refl _ end.

End GroupoidOperations.
Notation congr := ap.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.
Register eq_elim as core.eq.rect.
Register eq_sym as core.eq.sym.
Register eq_trans as core.eq.trans.
Register congr as core.eq.congr.

Definition eq_elim_r@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{_ β | _} y x -> P y :=
  fun px y e =>
    match e in _ = x return P x -> P y with
    | eq_refl => fun py => py
    end px.

Register eq_elim_r as core.eq.poly_r.

Definition eq_rect_r@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{α Type|_} y x -> P y :=
  fun px y e =>
  match e in _ = x return P x -> P y with
  | eq_refl => fun py => py
  end px.

Register eq_rect_r as core.eq.rect_r.

Definition eq_singleton_r@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, y = x -> P y :=
  fun px y e =>
    match e in _ = x return P x -> P y with
    | eq_refl => fun py => py
    end px.

Definition eq_ind_r@{α|u|} := eq_singleton_r@{α Prop | u Set}.

Register eq_ind_r as core.eq.ind_r.

Definition eq_elim_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{_ β |_} x y -> P y :=
  fun px y e =>
    match e in _ = y return P x -> P y with
    | eq_refl => fun px => px
    end px.

Register eq_elim_d as core.eq.poly.

Definition eq_rect_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{α Type|_} x y -> P y :=
  fun px y e =>
  match e in _ = y return P x -> P y with
  | eq_refl => fun py => py
  end px.

Register eq_rect_r as core.eq.rect.

Definition eq_ind_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, x = y -> P y := eq_singleton (fun y _ => P y).

Register eq_ind_d as core.eq.ind.

Definition f_equal@{s s' e|u v|} {A : Type@{s|u}} {B : Type@{s'|v}} (f : A -> B) {x y} : eq@{_ e| _} x y -> eq@{_ e| _} (f x) (f y) :=
  fun e => match e with | eq_refl => eq_refl end.

Register f_equal as core.eq.congr.

Definition f_equal2@{s1 s2 s' e|u1 u2 v|}
  {A1 : Type@{s1|u1}}
  {A2 : Type@{s2|u2}}
  {B : Type@{s'|v}}
  (f:A1 -> A2 -> B)
  {x1 y1:A1} {x2 y2:A2} :
  eq@{_ e|_} x1 y1 ->
  eq@{_ e|_} x2 y2 ->
  eq@{_ e|_} (f x1 x2) (f y1 y2) :=
  fun e1 => match e1 with | eq_refl => fun e2 => match e2 with | eq_refl => eq_refl end end.

Register f_equal2 as core.eq.congr2.
