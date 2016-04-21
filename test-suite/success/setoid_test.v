(* Require Import TestSuite.admit. *)
Require Import Setoid.

Parameter A : Set.

Axiom eq_dec : forall a b : A, {a = b} + {a <> b}.

Inductive set : Set :=
  | Empty : set
  | Add : A -> set -> set.

Fixpoint In (a : A) (s : set) {struct s} : Prop :=
  match s with
  | Empty => False
  | Add b s' => a = b \/ In a s'
  end.

Definition same (s t : set) : Prop := forall a : A, In a s <-> In a t.

Lemma setoid_set : Setoid_Theory set same.

unfold same; split ; red.
red; auto.

red.
intros.
elim (H a); auto.

intros.
elim (H a); elim (H0 a).
split; auto.
Qed.

Add Setoid set same setoid_set as setsetoid.

Add Morphism In : In_ext.
unfold same; intros a s t H; elim (H a); auto.
Qed.

Lemma add_aux :
 forall s t : set,
 same s t -> forall a b : A, In a (Add b s) -> In a (Add b t).
unfold same; simple induction 2; intros.
rewrite H1.
simpl; left; reflexivity.

elim (H a).
intros.
simpl; right.
apply (H2 H1).
Qed.

Add Morphism Add : Add_ext.
split; apply add_aux.
assumption.

rewrite H.
reflexivity.
Qed.

Fixpoint remove (a : A) (s : set) {struct s} : set :=
  match s with
  | Empty => Empty
  | Add b t =>
      match eq_dec a b with
      | left _ => remove a t
      | right _ => Add b (remove a t)
      end
  end.

Lemma in_rem_not : forall (a : A) (s : set), ~ In a (remove a (Add a Empty)).

intros.
setoid_replace (remove a (Add a Empty)) with Empty.

auto.

unfold same.
split.
simpl.
case (eq_dec a a).
intros e ff; elim ff.

intros; absurd (a = a); trivial.

simpl.
intro H; elim H.
Qed.

Parameter P : set -> Prop.
Parameter P_ext : forall s t : set, same s t -> P s -> P t.

Add Morphism P : P_extt.
intros; split; apply P_ext; (assumption || apply (Seq_sym _ _ setoid_set); assumption).
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
Definition rel : forall A : Set, relation (id A) := @eq.
Definition f: forall A : Set, A -> A := fun A x => x.

Add Relation (id A) (rel A) as eq_rel.

Add Morphism (@f A) : f_morph.
Proof.
unfold rel, f. trivial.
Qed.

(* Submitted by Nicolas Tabareau *)
(* Needs unification.ml to support environments with de Bruijn *)

Require Import Morphisms.

Instance proper_proxy_related_proxy A (R : relation A) m :
  ProperProxy R m -> RelatedProxy R m m := fun x => x.

Instance related_proxy_related A (R : relation A) m m' :
  Related R m m' -> RelatedProxy R m m' := fun x => x.

Instance proper_related A (R : relation A) m :
  Proper R m -> Related R m m := fun x => x.

Instance related_lam A (R : relation A) B (S : relation B) b b' :
  (forall x y (H : R x y), Related S (b x) (b' y)) ->
  Related (R ==> S)%signature (fun x : A => b x) (fun x : A => b' x).
Proof. intros H; intros x y. apply H. Defined.

Instance pointwise_resp' A B (R : relation B) :
  subrelation (@eq A ==> R)%signature  (pointwise_relation A R).
Proof. reduce. apply H. reflexivity. Defined.
Local Open Scope signature.
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
  Context (fold_lemma : forall {A B f} {eqA : relation B} x, eqA (fold A B f (add A x)) (fold _ _ f x)).
  Context (ab : forall B, A -> B).
  Context (anat : forall A, nat -> A).

Goal forall x, (fold _ _ (fun x => ab A x) (add A x) = anat _ (fold _ _ (ab nat) (add _ x))). 
Proof. intros.
  setoid_rewrite fold_lemma. 
  change (fold A A (fun x0 : A => ab A x0) x = anat A (fold A nat (ab nat) x)).
Abort.
End mult.

(** Real fold morphisms *)

Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)
  
  Context {A B : Type}.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 nil nil
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  Hint Constructors Forall2.
End Forall2.
Section Fold_Right_Recursor.
  Context {A : Type} {B : Type}.
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

Instance fold_proper A B (R : relation A) (S : relation B) :
  Proper ((R ==> S ==> S) ==> S ==> Forall2 R ==> S) (@fold_right B A).
Proof.
  reduce. induction H1; simpl; auto.
  apply H; auto.
Qed.

Definition natop acc n := acc + n.

Instance Forall2_refl A (R : relation A) (HR : Reflexive R) : Reflexive (Forall2 R).
Proof. intro. induction x; now constructor. Qed.

Lemma plus_comm : forall x y, plus x y = y + x.
Admitted.
Lemma mult_0 : forall x , x * 0 = 0.
Admitted.

Instance respectful_Transitive A B (R : relation A) (S : relation B) :
  Reflexive R -> Transitive S -> Transitive (R ==> S)%signature.
Proof.
  intros. reduce.
  transitivity (y x0).
  auto. auto.
Qed.

Lemma fold_proper_test l : fold_right (fun x y => plus x y + 0) 0 l = 0.
Proof.
  setoid_rewrite plus_comm.
  Show Proof.
  change(fold_right (fun x y : nat => 0 + (x + y)) 0 l = 0).
Abort.


Lemma fold_proper_test' l : fold_right (fun x y => plus x y) 0 l = 0.
Proof.
  Set Typeclasses Debug.
  setoid_rewrite plus_comm.
  Show Proof.
  change(fold_right (fun x y : nat => y + x) 0 l = 0).
Abort.

Axiom T : Type.
Axiom R : relation T.
Axiom Req : Equivalence R.
Axiom op : T -> T -> T.
Axiom opProper: Proper (R ==> R ==> R) op.
Axiom unit : T.
Axiom law : forall t, R (op t unit) t.
Axiom lawcomm : forall t t', R (op t t') (op t' t).

Lemma fold_proper_test' l :
  R (fold_right (fun x y => op x unit) unit l) unit.
Proof.
  setoid_rewrite lawcomm.
  change(R (fold_right (fun x _ : T => op unit x) unit l) unit).
Abort.

Axiom Rfinish : forall l, R l unit.

Lemma fold_proper_test'' l :
  R (fold_right (fun x y => op (op x y) unit) unit l) unit.
Proof.
  Time setoid_rewrite lawcomm.
  change(R (fold_right (fun x y : T => op unit (op x y)) unit l) unit).
  apply Rfinish.
Defined.

Lemma fold_proper_test''' l :
  R (fold_right (fun x y => op (op x y) unit) unit l) unit.
Proof.
  Time setoid_rewrite law.
  change(R (fold_right (fun x y : T => op x y) unit l) unit).
  apply Rfinish.
Defined.

(** Current semantics for rewriting with typeclass constraints in the lemma 
   does not fix the instance at the first unification, use [at], or simply rewrite for 
   this semantics. *)

Parameter beq_nat : forall x y : nat, bool.

Class Foo (A : Type) := {foo_neg : A -> A ; foo_prf : forall x : A, x = foo_neg x}.
Instance: Foo nat. Admitted.
Instance: Foo bool. Admitted.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) 0 = foo_neg y.
Proof. intros. setoid_rewrite <- foo_prf. change (beq_nat x 0 = y). Abort.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) 0 = foo_neg y.
Proof. intros. setoid_rewrite <- @foo_prf at 1. change (beq_nat x 0 = foo_neg y). Abort.

(* This should not raise an anomaly as it did for some time in early 2016 *)

Definition t := nat -> bool.
Definition h (a b : t) := forall n, a n = b n.

(* Instance subrelh : subrelation h (@eq nat ==> eq). *)
(* Proof. intros x y H x' y' ->. apply H.  Qed. *)

Goal forall a b, h a b -> a 0 = b 0.
intros.
rewrite H. (* Fallback on ordinary rewrite without anomaly *)
reflexivity.
Qed.
