(* Apply a theorem modulo isomorphism *)
(* By Théo Zimmermann 2015 *)

Require Export Coq.Classes.StandardInstances.
Require Coq.Classes.Respectful.

Typeclasses Opaque forall_def arrow.
(** universe-polymorphic forall_def and arrow are not declared as opaque in the library *)

(* Strict subrelation *)
Class HeteroSubrel {A B : Type} (R R' : A -> B -> Type) :=
  is_heteroSubrel : forall {x y}, R x y -> R' x y.

Generalizable Variables t u.

Theorem modulo `{class : Related _ _ impl t u} : t -> u.
Proof.
  lazy beta delta in class.
  tauto.
Qed.

Tactic Notation "exactm" constr(t) := exact (modulo t).
Tactic Notation "applym" constr(t) :=
  let H := fresh in
  pose (H := t); apply modulo in H; apply H; clear H.
Tactic Notation "transfer" := apply modulo.

Theorem modulo' `{class : Related _ _ arrow t u} : t -> u.
Proof.
  lazy beta delta in class.
  tauto.
Qed.

Tactic Notation "exactm'" constr(t) := exact (modulo' t).
Tactic Notation "applym'" constr(t) :=
  let H := fresh in
  pose (H := t); apply modulo' in H; apply H; clear H.
Tactic Notation "transfer'" := apply modulo'.

(* RULES *)

(* ENV *)

Ltac env_rule _ t t' :=
  match goal with
    | [ p : _ t t' |- _ ] => eexact p
  end.

Hint Extern 1 (Related ?R ?t ?t') => env_rule R t t' : typeclass_instances.

(* SUBREL *)

Instance subrel_rule
  (A B : Type)
  (R R' : A -> B -> Type)
  (t : A) (t' : B)
  (subrel_inst : HeteroSubrel R R')
  (inst : Related R t t') :
  Related R' t t' | 9 :=
  { related_prf := is_heteroSubrel related_prf }.

(* LAMBDA *)

Instance lambda_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (t : A -> C) (t' : B -> D)
  (inst : forall (x : A) (x' : B), R x x' -> Related R' (t x) (t' x')) :
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x') | 3 :=
  { related_prf := fun (x : A) (x' : B) (H : R x x') => @related_prf _ _ _ _ _ (inst x x' H) }.

Hint Extern 0 (Related _ _ _) => progress intros ** : typeclass_instances.

(* APP *)

Instance app_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) (e : A) (e' : B)
  (inst_f : Related (R ##> R') f f') (inst_e : Related R e e') :
  Related R' (f e) (f' e') | 2 :=
  { related_prf := (@related_prf _ _ _ _ _ inst_f) e e' (@related_prf _ _ _ _ _ inst_e) }.

(* ARROW *)

Instance arrow_rule
         (R : Type -> Type -> Type)
         (t1 t2 t1' t2' : Type)
         (inst : Related R (arrow t1 t2) (arrow t1' t2')) :
  Related R (t1 -> t2) (t1' -> t2') | 2 := inst.

Instance impl_rule
         (R : Prop -> Prop -> Prop)
         (t1 t2 t1' t2' : Prop)
         (inst : Related R (impl t1 t2) (impl t1' t2')) :
  Related R (t1 -> t2) (t1' -> t2') | 2 := inst.

(* FORALL *)

Instance forall_rule
  (R : Type -> Type -> Type)
  (t1 t1' : Type) (t2 : t1 -> Type) (t2' : t1' -> Type)
  (inst : Related R (forall_def (fun x : t1 => t2 x)) (forall_def (fun x' : t1' => t2' x'))) :
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3 := inst.

Instance all_rule
  (R : Prop -> Prop -> Prop)
  (t1 t1' : Type) (t2 : t1 -> Prop) (t2' : t1' -> Prop)
  (inst : Related R (all (fun x : t1 => t2 x)) (all (fun x' : t1' => t2' x'))) :
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3 := inst.

(* Subrelations *)

Instance sub_impl_arrow : HeteroSubrel impl arrow.
Proof ltac:(firstorder).

Instance sub_flip_impl_flip_arrow : HeteroSubrel (flip impl) (flip arrow).
Proof ltac:(firstorder).

Instance sub_iff_iffT : HeteroSubrel iff iffT.
Proof ltac:(firstorder).

Instance sub_iffT_arrow : HeteroSubrel iffT arrow.
Proof iffT_arrow_subrelation.

Instance sub_iffT_flip_arrow : HeteroSubrel iffT (flip arrow).
Proof iffT_flip_arrow_subrelation.

Instance sub_iff_impl : HeteroSubrel iff impl.
Proof ltac:(firstorder).

Instance sub_iff_flip_impl : HeteroSubrel iff (flip impl).
Proof ltac:(firstorder).

Instance sub_respectful_left
  (A B C D : Type)
  (R1 R2 : A -> B -> Type) (R' : C -> D -> Type) :
  HeteroSubrel R1 R2 -> HeteroSubrel (R2 ##> R') (R1 ##> R').
Proof ltac:(firstorder).

Instance sub_respectful_right
  (A B C D : Type)
  (R : A -> B -> Type) (R1' R2' : C -> D -> Type) :
  HeteroSubrel R1' R2' -> HeteroSubrel (R ##> R1') (R ##> R2').
Proof ltac:(firstorder).

(* Predefined instances *)

Ltac related_basics :=
  intros;
  unfold Related;
  unfold respectful_arrow;
  unfold arrow;
  unfold impl;
  unfold forall_def;
  unfold flip.

Ltac related_tauto :=
  related_basics;
  tauto.

Instance iffT_reflexivity : forall (A : Type), Related iffT A A | 10.
Proof ltac:(firstorder).

Instance true_rule : Related iff True True.
Proof ltac:(related_tauto).

Instance arrow_transfer_rule : Related (iffT ##> iffT ##> iffT) arrow arrow.
Proof arrow_arrow.

Instance impl_transfer_rule : Related (iff ##> iff ##> iff) impl impl.
Proof impl_impl.

Instance iff_rule : Related (iff ##> iff ##> iff) iff iff.
Proof iff_iff.

Instance prod_rule : Related (iffT ##> iffT ##> iffT) prod prod.
Proof prod_prod.

Instance and_rule : Related (iff ##> iff ##> iff) and and.
Proof and_and.

Instance or_rule : Related (iff ##> iff ##> iff) or or.
Proof or_or.

Instance eq_rule :
  forall (A : Type),
  Related (eq ##> eq ##> iff) (@eq A) (@eq A).
Proof eq_eq.

Instance eq_reflexivity :
  forall (A : Set) (x : A), Related eq x x.
Proof ltac:(reflexivity).

(** ** Totality declarations *)

Instance bitotal_from_bitotal
  (A B : Type)
  (R : A -> B -> Type)
  (inst : Related ((R ##> iffT) ##> iffT) forall_def forall_def) :
  Related ((R ##> iff) ##> iff) (@all A) (@all B).
Proof.
  unfold Related in *.
  apply Respectful.bitotal_decl.
  now apply bitotal_decl_recip1.
  now apply bitotal_decl_recip2.
Qed.
  
Instance bitotal_predicate_rule
  (A B : Type)
  (R : A -> B -> Type)
  (inst : Related (R ##> R ##> iff) eq eq) :
  Related (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)).
Proof.
  unfold Related in *.
  now apply Respectful.total_predicate.
Qed.

Instance bitotal_predicate_rule'
  (A B : Type)
  (R : A -> B -> Type)
  (inst : Related (R ##> R ##> iffT) eq eq) :
  Related (((R ##> iffT) ##> iffT) ##> iffT) forall_def forall_def.
Proof.
  unfold Related in *.
  now apply total_predicate.
Qed.