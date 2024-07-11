(*Require Import TestSuite.admit.*)

Axiom proof_admitted : empty.
Ltac admit := case proof_admitted.

Require Import Setoid.
Import Morphisms.
Require Import Coq.Classes.Morphisms_Prop.

Unset Universe Polymorphism.

Module TestSProp.

(** listings: same **)
Parameter A : Type.

Inductive set : Type :=
| Empty : set
| Add : A -> set -> set.

Fixpoint In (a : A) (s : set) {struct s} : SProp :=
  match s with
  | Empty => empty
  | Add b s' => {a = b} + {In a s'}
  end.

Definition same (s t : set) : SProp := forall a : A, In a s <-> In a t.
(** listings: end **)

  Instance same_Symmetric : Symmetric same.
  Proof.
    red; unfold same; intros. symmetry. eauto.
  Qed.

  Instance same_Refl : Reflexive same.
  Proof.
    red; unfold same; intros; reflexivity.
  Qed.

  Lemma add_aux :
 forall s t : set,
 same s t -> forall a b : A, In a (Add b s) -> In a (Add b t).
unfold same; destruct 2; intros.
destruct e.
simpl; left; reflexivity.

elim (H a).
intros.
simpl; right.
apply (fst i).
Qed.

(** listings: add_ext **)
Instance Add_ext : Proper (eq ++> same ++> same) Add.
(** listings: end **)
  intros x ? <- a b r.
  split; apply add_aux.
  assumption. symmetry; trivial.
  Qed.

(** listings: P_ext **)
Parameter P : set -> SProp.
Parameter P_ext : forall s t : set, same s t -> P s -> P t.
Instance P_extt : Proper (same ++> iff) P.
(** listings: end **)
intros; split; apply P_ext; [assumption | apply symmetry; assumption].
  Qed.

(** listings: test_rewrite **)
Lemma test_rewrite: forall (a : A) (s t : set), same s t -> P (Add a s) -> P (Add a t).
Proof.
  intros. setoid_rewrite <- H. trivial.
Qed.
(** listings: end **)

End TestSProp.

Parameter A : Set.

Axiom eq_dec : forall a b : A, {a = b} + {a <> b}.

Inductive set : Set :=
  | Empty : set
  | Add : A -> set -> set.

Fixpoint In (a : A) (s : set) {struct s} : Prop :=
  match s with
  | Empty => Empty.Empty
  | Add b s' => {a = b} + {In a s'}
  end.

Definition same (s t : set) : Prop := forall a : A, iff (In a s) (In a t).

Instance setoid_set : Equivalence@{Type Prop|_ _} same.
unfold same; split; red.
- tauto.
- intros. destruct (H a); split; auto.
- intros. destruct (H a); destruct (H0 a); split; auto.
Qed.

Instance In_ext : Proper@{Type Prop|Set+1 Set} (eq@{Type Prop|_} ++> same ++> iff@{Prop | Set Set}) In.
Proof.
  unfold same.
  intros x y a s t H.
  destruct a.
  destruct (H x).
  tauto.
Qed.

Lemma add_aux :
 forall s t : set,
 same s t -> forall a b : A, In a (Add b s) -> In a (Add b t).
unfold same; destruct 2; intros.
rewrite e.
simpl; left; reflexivity.

elim (H a).
intros.
simpl; right.
apply (fst i).
Qed.

Instance Add_ext : Proper@{Type Prop|_ _} (eq ++> same ++> same) Add.
intros x ? <- a b r.
split; apply add_aux.
assumption.
rewrite r. reflexivity.
Qed.

Fixpoint remove (a : A) (s : set) {struct s} : set :=
  match s with
  | Empty => Empty
  | Add b t =>
      match eq_dec a b with
      | left _ _ => remove a t
      | right _ _ => Add b (remove a t)
      end
  end.

Goal exists A, (@Proper@{Type Prop | Set+1 Set}
           (Prop -> Prop) A not@{Prop | Set}).
econstructor.
set (foo := do_subrelation).
(* apply (not_iff_morphism). *)
typeclasses eauto.
Show Proof.
Qed.

Lemma in_rem_not : forall (a : A) (s : set), not@{Prop|Set} (In a (remove a (Add a Empty))).

intros.

setoid_replace (remove a (Add a Empty)) with Empty.
- intros [].
- unfold same.
split.
simpl.
case (eq_dec a a).
intros e ff; destruct ff.

intros. apply n. reflexivity.

simpl.
intros [].
Qed.

Parameter P : set -> Prop.
Parameter P_ext : forall s t : set, same s t -> P s -> P t.

Instance P_extt : Proper (same ++> iff) P.
intros; split; apply P_ext; (assumption || apply symmetry; assumption).
Qed.

Lemma test_rewrite :
 forall (a : A) (s t : set), same s t -> P (Add a s) -> P (Add a t).
intros.
rewrite <- H.
rewrite H.
setoid_rewrite <- H.
setoid_rewrite H.
setoid_rewrite <- H.
trivial.
Qed.

(* Unifying the domain up to delta-conversion (example from emakarov) *)

Definition id: Set -> Set := fun A => A.
Definition rel : forall A : Set, relation@{Type Prop|_ Set} (id A) := @eq.
Definition f: forall A : Set, A -> A := fun A x => x.
(*
Instance eq_rel_relation {A : Set} : @RewriteRelation@{Type Prop | Set Set} (id A)
  (@eq@{Type Prop | Set Set} A).
Qed. *)

Instance f_morph : Proper (eq ++> eq) (@f A).
Proof.
intros ? ? ?.
trivial.
Qed.

(* Submitted by Nicolas Tabareau *)
(* Needs unification.ml to support environments with de Bruijn *)

Goal forall
  (f : Prop -> Prop)
  (Q : (nat -> Prop) -> Prop)
  (H : forall (h : nat -> Prop), Q (fun x : nat => f (h x)) <-> True)
  (h:nat -> Prop),
  Q (fun x : nat => f (Q (fun b : nat => f (h x)))) <-> True.
intros f0 Q H.
setoid_rewrite H.
tauto.
Qed.

(** Check proper refreshing of the lemma application for multiple 
   different instances in a single setoid rewrite. *)

Section mult.
  Context (fold : forall {A} {B}, (A -> B) -> A -> B).
  Context (add : forall A, A -> A).
  Context (fold_lemma : forall {A B f} {eqA : relation@{Type Prop|Set Set} B} x, eqA (fold A B f (add A x)) (fold _ _ f x)).
  Context (ab : forall B, A -> B).
  Context (anat : forall A, nat -> A).
Goal forall x, (fold _ _ (fun x => ab A x) (add A x) = anat _ (fold _ _ (ab nat) (add _ x))). 
Proof. intros.
  setoid_rewrite fold_lemma. 
  change (fold A A (fun x0 : A => ab A x0) x = anat A (fold A nat (ab nat) x)).
Abort.

End mult.

(** Current semantics for rewriting with typeclass constraints in the lemma 
   does not fix the instance at the first unification, use [at], or simply rewrite for 
   this semantics. *)

Parameter beq_nat : forall x y : nat, bool.

Class Foo (A : Type) := {foo_neg : A -> A ; foo_prf : forall x : A, x = foo_neg x}.
#[export] Instance: Foo nat. admit. Defined.
#[export] Instance: Foo bool. admit. Defined.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) O = foo_neg y.
Proof. intros. setoid_rewrite <- foo_prf. change (beq_nat x O = y). Abort.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) O = foo_neg y.
Proof. intros. setoid_rewrite <- @foo_prf at 1. change (beq_nat x O = foo_neg y). Abort.

(* This should not raise an anomaly as it did for some time in early 2016 *)

Definition t := nat -> bool.
Definition h (a b : t) := forall n, a n = b n.

#[export] Instance subrelh : subrelation h (Morphisms.pointwise_relation nat eq).
Proof. intros x y H; assumption. Qed.

Goal forall a b, h a b -> a O = b O.
intros.
setoid_rewrite H. (* Fallback on ordinary rewrite without anomaly *)
reflexivity.
Qed.

Module InType.

Inductive All {A : Type} (P : A -> Type) : list A -> Type :=
| All_nil : All P nil
| All_cons x (px : P x) xs (pxs : All P xs) : All P (x :: xs).

Lemma All_impl {A} (P Q : A -> Type) l : (forall x, P x -> Q x) -> All P l -> All Q l.
Proof.
  intros HP. induction 1; constructor; eauto.
Qed.

Axiom add_0_r_peq : forall x : nat, eq (plus x O)%nat x.

#[export] Instance All_proper {A} :
  Morphisms.Proper ((pointwise_relation A iff) ++> eq ++> iff) All.
Proof.
  intros f g Hfg x y e. destruct e. split; apply All_impl, Hfg.
Qed.

Lemma rewrite_all {l : list nat} (Q : nat -> Type) :
  All (fun x => Q x) l ->
  All (fun x => Q (plus x O)) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq.
  exact a.
Qed.

Lemma rewrite_all_in {l : list nat} (Q : nat -> Type) :
  All (fun x => Q (plus x O)) l ->
  All (fun x => Q x) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.

Lemma rewrite_all_in2 {l : list nat} (Q : nat -> Type) (R : nat -> Type) :
  All (fun x => prod (Q (plus x O)%nat) (R x))%type l ->
  All (fun x => prod (Q x) (R x))%type l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.
End InType.

Module Polymorphism.

Notation "x :: xs" := (cons x xs).

#[universes(polymorphic)]
Fixpoint All@{i j} {A : Type@{i}} (P : A -> Type@{j}) (l : list A) : Type@{j} :=
 match l with
 | nil => unit
 | x :: xs => prod (P x) (All P xs)
 end.

#[universes(polymorphic)]
Lemma All_impl {A} (P Q : A -> Type) l : (forall x, P x -> Q x) -> All P l -> All Q l.
Proof.
  intros HP.
  induction l using list_elim; [intros|intros []]; constructor; eauto.
Qed.
Check pointwise_relation.

#[universes(polymorphic)]
Axiom add_0_r_eq : forall x : nat, eq (plus x O)%nat x.

#[universes(polymorphic), export]
Instance All_proper {A} :
  Morphisms.Proper ((pointwise_relation A iff) ++> eq ++> iff) All.
Proof.
  intros f g Hfg x y e. destruct e. split; apply All_impl, Hfg.
Qed.

Lemma rewrite_all {l : list nat} (Q : nat -> Type) :
  All (fun x => Q x) l ->
  All (fun x => Q (plus x O)) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_eq.
  exact a.
Qed.

Lemma rewrite_all_in {l : list nat} (Q : nat -> Type) :
  All (fun x => Q (plus x O)) l ->
  All (fun x => Q x) l.
Proof.
  intros a.  Show Universes.
  setoid_rewrite add_0_r_eq in a.
  exact a.
Qed.
Check rewrite_all_in@{Set}.

Lemma rewrite_all_in2 {l : list nat} (Q : nat -> Type) (R : nat -> Type) :
  All (fun x => prod (Q (plus x O)%nat) (R x))%type l ->
  All (fun x => prod (Q x) (R x))%type l.
Proof.
  intros a.
  setoid_rewrite add_0_r_eq in a.
  exact a.
Qed.
Check rewrite_all_in2@{0 0}.

End Polymorphism.
