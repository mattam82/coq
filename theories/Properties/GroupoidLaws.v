From Corelib Require Import Prelude.
From Corelib Require Import Types.
From Corelib.Classes Require Import Morphisms Morphisms_Prop Equivalence.
From Corelib Require Import Setoid.

(** Leibniz equality. *)
Section Leibniz.

  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_leibniz: Has_Leibniz@{sa se se|la le le} eq} {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}.

  Lemma proper_eq (x : A) : Proper (eq A) x.
  Proof. intros. apply reflexive_proper. Qed.

End Leibniz.

Definition gen_st : forall A : Set, Setoid_Theory _ (@eq A).
Proof.
  constructor; typeclasses eauto.
Qed.

Ltac proper_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | _ => class_apply proper_eq || class_apply @reflexive_proper
  end.

#[global]
  Hint Extern 7 (@Proper _ _ _) => proper_reflexive
    : typeclass_instances.

(*
#[global]
Hint Immediate eq_sym not_eq_sym: core.
*)

Instance Proper_eq@{sa se sp|la le lp|} {eq} (A:Type@{sa|la})
  `{Has_Leibniz@{sa se sp|la le lp} eq}
  `{Has_Leibniz@{sa se se|la le le} eq}
  `{Has_refl@{sa se|la le} eq}
   (P:A -> Type@{sp|lp}) : Proper (eq A ++> flip arrow@{sp sp | lp lp}) P.
Proof.
compute. intros. eapply leibniz; eauto. eapply _eq_sym; eauto.
Defined.

Definition eq_elim_r@{sa se sp|la le lp|} {eq} (A:Type@{sa|la})
  `{Has_Leibniz@{sa se sp|la le lp} eq}
  `{Has_Leibniz@{sa se se|la le le} eq}
  `{Has_refl@{sa se|la le} eq}
  (x:A) (P:A -> Type@{sp|lp}) :
  P x -> forall y:A, eq A y x -> P y.
  intros px y e. setoid_rewrite e; eauto. Defined.

Register eq_elim_r as core.eq.poly_r.

(*
  Definition eq_rect_r@{α β|u v ? | ? } (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{α Type|_} y x -> P y := fun px y e => eq_elim_r@{α Type β| u u v} _ _ _ px _ e.
*)

Definition eq_rect_r@{α β | u v |} A x P px y e :=
  @eq_elim_r@{α Type β | u u v} (@eq) A
    (* eq_Has_LeibnizType *)
    (fun A x P Px y e => eq_Has_LeibnizType A x P Px y e)
    (fun A x P Px y e => eq_Has_LeibnizType A x P Px y e) eq_Has_refl x P px y e.

Register eq_rect_r as core.eq.rect_r.

Definition eq_singleton_r@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, y = x -> P y :=
  fun px y e =>
    match e in _ = x return P x -> P y with
    | eq_refl => fun py => py
    end px.

Definition eq_ind_r@{α|u|} := eq_singleton_r@{α Prop | u Set}.

Register eq_singleton_r as core.eq.ind_r.

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

Register eq_rect_d as core.eq.rect.

Definition eq_ind_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, x = y -> P y := eq_singleton (fun y _ => P y).

Register eq_ind_d as core.eq.ind.

Definition f_equal@{s s' e|u v |} {A : Type@{s|u}} {B : Type@{s'|v}} (f : A -> B) {x y} : eq@{_ e| _} x y -> eq@{_ e| _} (f x) (f y)
  := ap@{s e s' e|u u v v} (_leibniz := eq_Has_Leibniz_elim) f.

Register f_equal as core.eq.congr.

Arguments f_equal [_ _] _ [_ _] _.

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

Arguments f_equal2 [_ _ _] _ [_ _ _ _] _ _.


Module GroupoidNotations.

(* Notation " e ▷ t " := (ltac:(exact (tr e t) + exact (tr (eq_sym e) t))) (at level 70, only parsing).*)

Notation "e1 ⋅ e2" := (eq_trans e1 e2) (at level 65, right associativity).
End GroupoidNotations.
Import GroupoidNotations.

Section GroupoidLaws.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
        {_leibniz: Has_Leibniz@{sa se se|la le le} eq}
        {_refl: Has_refl@{sa se|la le} eq}
        {_J: Has_J@{sa se se|la le le} eq _}
        {eq' : forall A : Type@{se | le}, A -> A -> Type@{se|le}}
        {J_refl : Has_JRefl@{sa se se se|la le le le} eq _ _J _leibniz eq'}
        {_refl': Has_refl@{se se|le le} eq'}
        {_leibniz': Has_Leibniz@{se se se |le le le} eq'}
        {_J': Has_J@{se se se |le le le} eq' _}
        {A : Type@{sa|la}}.

  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq' _ x y) : type_scope.
  #[warnings="-notation-overridden"]
  Local Notation "x = y :> A" := (eq A x y) : type_scope.

  Definition runit {x y : A} (e : x = y :> A) : e ⋅ refl A y = e.
  Proof. eapply leibniz_refl. Defined.

  Definition lunit {x y : A} (e : x = y :> A) : refl A x ⋅ e = e.
  Proof. apply J with (P := fun y e => refl A x ⋅ e = e). apply runit. Defined.

(** listings: eqassoc **)
Definition assoc {x y z w : A} (e1 : x = y :> A) (e2 : y = z :> A) (e3 : z = w :> A) :
    e1 ⋅ (e2 ⋅ e3) = (e1 ⋅ e2) ⋅ e3.
(** listings: end **)
Proof. apply J with (P := fun w e3 => e1 ⋅ e2 ⋅ e3 = (e1 ⋅ e2) ⋅ e3).
  etransitivity. { unshelve eapply ap; try eassumption. unshelve eapply leibniz_refl. }
  symmetry. unshelve eapply leibniz_refl.
Qed.

  Definition inv_refl {x : A} : eq_sym (refl A x) = (refl A x : eq A x x).
  Proof. apply leibniz_refl with (P :=fun y0 : A => y0 = x :> A). Defined.

  Definition sym_lInv {x y : A} (e : x = y :> A) : eq_sym e ⋅ e = refl _ _.
  Proof. eapply J with (P := fun y e => eq_sym e ⋅ e = refl A y).
    setoid_rewrite runit. apply inv_refl. Defined.

  Definition sym_rInv {x y : A} (e : x = y :> A) : e ⋅ eq_sym e = refl _ _.
  Proof. eapply J with (P := fun y e => e ⋅ eq_sym e = refl A x).
    setoid_rewrite lunit. apply inv_refl. Defined.

  Definition inv_concat {x y z : A} (e : x = y :> A) (e' : y = z :> A) :
    eq_sym (e ⋅ e') = eq_sym e' ⋅ eq_sym e.
  Proof.
    revert e'. unshelve eapply J with (P := fun y e => forall e', eq_sym (e ⋅ e') = eq_sym e' ⋅ eq_sym e).
    intro e'. unshelve eapply J with (P := fun z e' => eq_sym (refl A x ⋅ e') = eq_sym e' ⋅ eq_sym (refl A x)).
    setoid_rewrite inv_refl. setoid_rewrite lunit. eapply inv_refl.
  Defined.

  Definition sym_sym {x y : A} (e : x = y :> A) : eq_sym (eq_sym e) = e.
  Proof.
    eapply J with (P := fun y e => eq_sym (eq_sym e) = e).
    repeat setoid_rewrite inv_refl. reflexivity.
  Defined.

  Sort sb.
  Universe b le' le''.
  Context {B : Type@{sb|b}} (f : A -> B)
  {eqB : forall A : Type@{sb | b}, A -> A -> Type@{se|le'}}
  {_reflB: Has_refl@{sb se|b le'} eqB}
  {_leibnizB: Has_Leibniz@{sa se se|la le le'} eq}
  {eq'' : forall A : Type@{se | le'}, A -> A -> Type@{se|le''}}
  {_refl'': Has_refl@{se se|le' le''} eq''}
  {J_refl' : Has_JRefl@{sa se se se|la le le le} eq _ _J _leibnizB eq''}.

(*  {J_refl : Has_JRefl@{sa se se se|la le le le} eq _ _J _leibniz eq'}
  {_leibniz': Has_Leibniz@{se se se |le le le} eq'}
  {_J': Has_J@{se se se |le le le} eq' _}  *)

  Definition ap_rfl {x : A} : eq'' (eqB _ _ _) (ap f (refl A x : eq _ _ _)) (refl B (f x)).
  Proof. eapply leibniz_refl with (P := fun y : A => eqB B (f x) (f y)). Defined.

  (*
  Definition ap_concat {x y z : A} (e1 : x = y :> A) (e2 : y = z :> A) :
    eq'' _ (ap f (e1 ⋅ e2)) (ap f e1 ⋅ ap f e2).
  Proof.
    induction e1 using eq_elim; reflexivity.
  Defined.

  Definition ap_eq_sym {x y : A} (e : x = y) : ap f (eq_sym e) = eq_sym (ap f e).
  Proof.
    induction e using eq_elim; reflexivity.
  Defined.
*)
End GroupoidLaws.


