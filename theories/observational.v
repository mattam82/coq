(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

From Corelib Require Import GroupoidLaws.

Notation "a ~ b" := (a = b :> _ : SProp) (at level 50).

Symbol cast@{α|u|} : forall (A B : Type@{α|u}), A ~ B -> A -> B.

Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

Instance eq_Has_Leibniz_elim@{α β|l l'|} : Has_Leibniz@{α SProp β|l 0 l'} (@eq) :=
 { leibniz := fun A x P px y e => cast (P x) (P y) (f_equal@{_ _ _|l l'+1} P e) px}.

Instance eq_Has_J_elim@{α β|l l'|} : Has_J@{α SProp β|l l l'} (@eq) _ :=
  { J := fun A a P t b e => cast (P a (refl _ _)) (P b e)
    (apd@{α β SProp SProp|l 0 l' 0} (_J := eq_Has_J_elim) P b e) t }.

Parameter obseq_forall_1@{s s'|?|?} :
  forall {A A' : Type@{s|_}} {B : A -> Type@{s'|_}} {B' : A' -> Type@{s'|_}},
    (forall (x : A), B x) ~ (forall (x : A'), B' x) -> A' ~ A.

Parameter obseq_forall_2@{s s'|?|?} : forall {A A' : Type@{s|_}} {B : A -> Type@{s'|_}} {B' : A' -> Type@{s'|_}}
  (e : (forall (x : A), B x) ~ (forall (x : A'), B' x)) (x : A'),
  B (obseq_forall_1 e # x) ~ B' x.

Parameter funext : forall {A B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.

Rewrite Rule cast_pi :=
| @{s|u ?|?} |- cast@{s|u} (forall (x : ?A), ?B) (forall (x : ?A'), ?B') ?e ?f
   => fun (x : ?A') => cast ?B@{x := cast ?A' ?A (obseq_forall_1@{_ _ |u u u u u} ?e) x}
                            ?B'@{x := x}
                            (obseq_forall_2@{_ _ | u u u u u u u u u} ?e x)
                            (?f (cast ?A' ?A (obseq_forall_1@{_ _ | u u u u u} ?e) x)).

(** Definition of the observational equality on strict propositions *)

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

(** Tests cast for functions *)

Opaque eq_sym.

Section Basic_Test.
  Sort s s'.
  Universe u v.
  Variable A B : Type@{s|u}.
  Variable C : A -> Type@{s'|v}.
  Variable D : B -> Type@{s'|v}.

  Variable obseq_fun1 : (forall a:A, C a) ~ (forall b:B, D b).
  Variable f : forall a:A, C a.
  Variable g : forall b:B, D b.

  (* remark that when the domain/codomain match, one of the casts is eliminated *)
  (* Eval simpl in (cast _ _(obseq_fun1) f). *)
  (* Eval lazy in (cast _ _ (eq_sym obseq_fun1) g). *)

End Basic_Test.

Lemma test {A:Type} (a b : A) (P : A -> Type) : a ~ b -> P a -> P b.
Proof.
  intros e Pa. setoid_rewrite <- e. auto.
Defined.
