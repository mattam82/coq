From Corelib Require Import Types.
From Corelib Require Import Classes.

Section GroupoidOperations.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_leibniz: Has_Leibniz@{sa se se|la le le} eq} {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}.

  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq _ x y) : type_scope.
  #[warnings="-notation-overridden"]
  Local Notation "x <> y" := (~ (eq _ x y)) : type_scope.

  Definition eq_sym {x y : A} (e : x = y) : y = x :=
    leibniz _ _ _ (fun y => y = x) (refl _ _) _ e.

  Definition eq_trans {x y z : A} (e1 : x = y) : y = z -> x = z :=
    fun e2 => leibniz _ _ _ (fun z => x = z) e1 _ e2.

  Definition not_eq_sym {x y : A} : x <> y -> y <> x :=
    fun ne e => ne (eq_sym e).

(*  Definition apD {B : A -> _} (f : forall (a:A), B a) {x y : A} (e : x = y) : eq' _ (f x) (f y) :=
      leibniz _ _ (fun y => eq' B (f x) (f y)) (refl _ _) _ e.
*)
    (*
   Definition tr@{b|} {B : Type@{sa|b}} (e : @eq@{_ sa|max(a+1,b+1)} Type@{sa|max(a,b)} A B) : A -> B :=
    match e in @eq _ _ B return A -> B with | eq_refl _ => fun x => x end.
*)

End GroupoidOperations.


(** Leibniz equality. *)
Section Leibniz.

  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_leibniz: Has_Leibniz@{sa se se|la le le} eq} {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}.

  Global Instance eq_Reflexive : Reflexive (@eq A) := refl A.
  Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym _ _ _ A.
  Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans _ _ A.

(*  Lemma proper_ap : Proper (Proper (eq A ++> flip arrow) P). *)

    (** Leibinz equality [eq] is an equivalence relation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)

  Global Program Instance eq_equivalence : Equivalence (eq A) | 10.
End Leibniz.

Notation congr := ap.

(* Aliases *)

Definition _eq_sym {A} {x y : A} (e : x = y) : y = x :=
    leibniz _ _ _ (fun y => y = x) (refl _ _) _ e.

Register _eq_sym as core.eq.sym.

Definition ind_eq_trans@{l} := @eq_trans@{Type Prop|l 0} (@eq) _.
Register ind_eq_trans as core.eq.trans.

Notation sym_eq := _eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := eq_refl (only parsing).
Notation sym_equal := _eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

#[export]
Hint Immediate _eq_sym not_eq_sym: core.

Definition eq_elim_r@{sa se sp|la le lp|} {eq} (A:Type@{sa|la})
  `{Has_Leibniz@{sa se sp|la le lp} eq}
  `{Has_Leibniz@{sa se se|la le le} eq}
  `{Has_refl@{sa se|la le} eq}
  (x:A) (P:A -> Type@{sp|lp}) :
  P x -> forall y:A, eq A y x -> P y.
Proof. compute. intros. eapply (leibniz eq); eauto. eapply eq_sym; eauto. Defined.

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
  := ap@{s e s' e|u u v v} (_leibniz := fun A x P Px y e => eq_Has_Leibniz_elim A x P Px y e) f.

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
