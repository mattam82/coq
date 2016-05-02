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
(*
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
*)
Require Import Morphisms.

Local Open Scope signature.

(* Goal forall *)
(*   (f : Prop -> Prop) *)
(*   (Q : (nat -> Prop) -> Prop) *)
(*   (H : forall (h : nat -> Prop), Q (fun x : nat => f (h x)) <-> True) *)
(*   (h:nat -> Prop), *)
(*   Q (fun x : nat => f (Q (fun b : nat => f (h x)))) <-> True. *)
(*   intros f0 Q H. *)
(*   setoid_rewrite H. *)
(*   tauto. *)
(* Qed. *)

Axiom cheat : forall {A}, A.

Ltac related_proper :=
  match goal with
  |- Related ?R ?x ?x => change (Proper R x)
  end.
Require Import Program.Tactics.

Goal forall (x y : nat) (P : nat -> Prop) (e : x = y), P y -> True -> P x.
Proof.
  intros x y P e H.
  setoid_rewrite debug e. trivial. 
  (* FIXME *)
  Abort.

Ltac forward H :=
  match type of H with
    | ?T -> _ => let HT := fresh "H" in assert(HT : T); [clear H|specialize (H HT); simpl in H; clear HT]
  end.

Notation " A '⇒' B " := (all (fun _ : A => B)) (at level 89).
Require Import Program.Basics.
Goal forall (x y : nat) (P Q : nat -> Prop) (e : x = y), P y -> Q x -> P x.
Proof.
  intros x y P Q e H.
  (* Tactic *)
  evar (R : Q x -> Q y -> Prop). clear R.
  assert (HR:Related
               (∀ _ : (∀ _ : ?R x y, flip impl) _ _, flip impl)  (@all (Q x)) (@all (Q y))).
(*   unshelve apply _. (* find the morphism for all *) *)
(*   now rewrite e. (* rewrite in the domain of the forall *) *)
(*   specialize (HR (fun _ => P x) (fun _ => P y)). *)
(*   forward HR. *)
(*   red. simpl. intros. red. red. now rewrite e. (* rewrite in the codomain *) *)
(*   (* Apply the morphism proof *) *)
(*   simpl in HR. unfold respectful_hetero in HR. *)
(*   apply HR. clear HR. unfold all. *)
(*   (* End of tactic *) *)
(*   intros; apply H. *)
(* Qed. *)
Abort.
Instance: Reflexive iff.
red. intros. split; intros; trivial. Defined.
Require Import Morphisms_Prop.

Section dependent_eq.
Variable P : nat -> Prop.
Variable dependent : forall n, P n -> Prop.

Variable dependent_mor :
  Proper (∀ H : eq n n', λ pn pn', flip impl) dependent.
Set Typeclasses Modulo Eta.


Goal forall (n n' : nat) (e : n = n') (H : forall (pn' : P n'), dependent n' pn')
       (pn : P n), dependent n pn.
Proof.
  intros n n' e pn' d.
  assert(P n') by now setoid_rewrite <- e.
  setoid_rewrite e.
  apply (pn' H).
Qed.

Goal forall (n n' : nat) (e : n = n') (H : forall (pn' : P n'), dependent n' pn')
       (pn : P n), dependent n pn.
Proof.
  intros n n' e pn' d. revert d.
  setoid_rewrite debug e. apply pn'.
  shelve. shelve. 
  (* refine (HasRetraction_rel _). *)
  clear H_rew.
  apply _.
  apply _.
Qed.
End dependent_eq.

Section dependent_abs.
  Variable nat : Type.
  Variable eq : nat -> nat -> Prop.
  Variable P : nat -> Prop.
  Variable dependent : forall n, P n -> nat.
  Variable ProperP : Proper (eq ==> iff) P.
  Variable Heq : Equivalence eq.
  Variable HR:Proper (∀ R : eq n n', λ _ _, eq) dependent.

  Goal forall (n n' : nat) (e : eq n n') 
         (pn : P n) (pn' : P n'), eq (dependent n pn) (dependent n' pn').
  Proof.
    intros n n' e pn pn'.
    setoid_rewrite e. apply reflexivity.
  Qed.
End dependent_abs.

Goal forall (x y : nat) (P Q : nat -> Prop) (e : x = y), P y -> Q x -> P x.
Proof.
  intros x y P Q e H.
  setoid_rewrite e. trivial.
Qed.


Goal forall (x y : nat) (P Q : nat -> Prop) (e : x = y), P y -> Q x -> P x.
Proof.
  intros x y P Q e H.
  set(R:=fun (p : Q x) (q : Q y) => True).
  assert (Related
            (∀ _ : (∀ _ : R x y, iff) _ _, iff)  (@all (Q x)) (@all (Q y))).
  clear.
  reduce. red in H.
  unfold all in *. split; intros.
  rewrite <- H. apply H0. unfold R. split.
  rewrite H. apply H0. red. split.
  specialize (H0 (fun _ => P x) (fun _ => P y)). simpl in H0.
  unfold respectful_hetero in H0.
  red in H0.
  unfold all in H0. apply H0.
  intros. rewrite e. reflexivity.
  intros; apply H.
Abort.

(** Check proper refreshing of the lemma application for multiple 
   different instances in a single setoid rewrite. *)

Section mult.
  Context (fold : forall {A} {B}, (A -> B) -> A -> B).
  Context (add : forall A, A -> A).
  Context (fold_lemma : forall {A B f} {eqA : relation B} x, eqA (fold A B f (add A x)) (fold _ _ f x)).
  Context (ab : forall B, A -> B).
  Context (anat : forall A, nat -> A).

Goal forall x, (fold _ _ (fun x => ab A x) (add A x) = anat _ (fold _ _ (ab nat) (add _ x))). 
Proof.
  intros.
  setoid_rewrite fold_lemma.
  change (fold A A (fun x0 : A => ab A x0) x = anat A (fold A nat (ab nat) x)).
  (* Order of resolution can matter... due to fake dependencies *)
Admitted.
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
Goal True.

Lemma fold_proper_test l : fold_right (fun x y => plus x y + 0) 0 l = 0.
Proof.
  setoid_rewrite plus_comm at 1.
  admit.
Abort.

Lemma fold_proper_test' l : fold_right (fun x y => plus x y) 0 l = 0.
Proof.
  setoid_rewrite plus_comm.
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
