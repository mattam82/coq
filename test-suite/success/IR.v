(* Inductive Pack A (R : A -> Type) := pack { *)
(*   TX : A; *)
(*   TR : R TX; *)
(*                                      }. *)
(* Definition Tel := *)
(*   fix Tel (p n : nat) {struct p} : Type := *)
(*     match p with *)
(*       0 => unit *)
(*     | S p => (unit * Tel p (S n))%type *)
(*     end *)
(*   with C (p n : nat) {struct n} : (* Tel p n -> *) Type := *)
(*     match n with *)
(*     | 0 => Tel p 0 *)
(*     | S n => (* fun T : Tel p (S n) => *) C (S p) n  (* ((tt,T)) *) *)
(*     end for Tel. *)

(* Inductive Tel : nat -> nat -> Type := *)
(* | Tel0 : forall n, Tel 0 n *)
(* | TelS : forall p n (T : Tel p (S n)), C p n (π p n T) -> Tel (S p) n *)

(* fix C {p n : nat} {struct n} : Tel p n -> Type := *)
(* match n with *)
(* | 0 => fun T => eval T -> Type *)
(* | S n => fun T => Pack (C (π T)) (fun A => @C (S p) n (TelS p n T A)) *)
(* end *)

(* fix π {p n : nat} (T : Tel p (S n)) : Tel p n := *)
(* match T with *)
(* | Tel0 (S n) => Tel0 n *)
(* | TelS p (S n) T A => TelS p n (@π p (S n) T) _ *)
(* end *)

(* fix eval {p : nat} (T : Tel p 0) : Type := *)
(* match T in Tel p n' return n' = 0 -> Type with *)
(* | Tel0 _ => fun _ => unit *)
(* | TelS p 0 T A => fun _ => Pack (@eval p (π T)) (fun x => A x) *)
(* | TelS p n T A => fun H => _ *)
(* end eq_refl. *)
Module SetUniv.

Inductive U : Set :=
| cunit : U
| cnat : U
| ceq u : El u -> El u -> U
| cprod (u : U) (f : El u -> U) : U
| csigma (u : U) : (El u -> U) -> U

fix El (u : U) : Set :=
  match u with
  | cunit => unit
  | cnat => nat
  | ceq U u v => u = v
  | cprod u f => forall x : El u, El (f x)
  | csigma u f => { u' : El u & El (f u') }
  end.
End SetUniv.


Module typeUniv.
Inductive U : Type :=
| cunit : U
| cset : Set -> U
| ceq u : El u -> El u -> U
| cprod (u : U) (f : El u -> U) : U
| csigma (u : U) : (El u -> U) -> U

fix El (u : U) : Set :=
  match u with
  | cunit => unit
  | cset X => X
  | ceq U u v => u = v
  | cprod u f => forall x : El u, El (f x)
  | csigma u f => { u' : El u & El (f u') }
  end.

Fixpoint fstU {u : U} : El u -> unit :=
  match u return El u -> unit with
  | cunit => fun x => x
  | cset _ => fun x => tt
  | ceq u x y => fun _ => tt
  | cprod u f => fun _ => tt
  | csigma u f => fun x => fstU (projT1 x)
  end.

Definition uinhab : U :=
  cprod (cset nat) (fun x => ceq _ x x).
Eval compute in El uinhab.

Definition uinhabprod : U :=
  csigma cunit (fun x => cunit).

End typeUniv.

Module MLUniv.
Inductive U : Type :=
| cunit : U
| cset : Set -> U
| ctype : Type -> U
| ceq u : El u -> El u -> U
| cprod (u : U) (f : El u -> U) : U
| csigma (u : U) : (El u -> U) -> U

fix El (u : U) : Type :=
  match u with
  | cunit => unit
  | cset X => X
  | ctype T => T
  | ceq U u v => u = v
  | cprod u f => forall x : El u, El (f x)
  | csigma u f => { u' : El u & El (f u') }
  end.

Definition uinhab : U :=
  cprod (cset nat) (fun x => ceq _ x x).
Eval compute in El uinhab.

Definition polyu : U :=
  cprod (ctype Set) (fun x => ceq _ x x).
Eval compute in El polyu.

Inductive funnylist : Set :=
| nil
| cons (x : nat) (l : funnylist) (p : greater x l)

fix greater (x : nat) (l : funnylist) : Prop :=
  match l with
  | nil => True
  | cons y _ _ => x > y
  end.

Require Import Arith.
Require Import Peano_dec.
Fixpoint inx (x : nat) (l : funnylist) :=
  match l with
  | nil => False
  | cons y l p =>
    match lt_eq_lt_dec x y with
    | inleft (left _) => inx x l
    | inleft (right _) => True
    | inright _ => False
    end
  end.

Inductive bla : Set :=
| consbla (x : nat) (g : blas x)

fix blas (x : nat) : Set :=
  match x with
  | 0 => unit
  | S n => (bla * blas n)
  end.


Section blaind.

  
  Context (P : bla -> Prop).

  Fixpoint Forallblas x : blas x -> Prop :=
    match x with
    | 0 => fun _ => True
    | S n => fun x => P (fst x) /\ (Forallblas n (snd x))
    end.

  Context (* (Pblas : forall x l, Forallblas x l) *)
          (Pc : forall (x : nat) (g : blas x), Forallblas x g -> P (consbla x g)).

  Definition foo : forall b : bla, P b.
  Proof.
    fix 1.
    destruct b. apply Pc.
    revert x g. fix 1. intros. destruct x. split.
    simpl in g. simpl.
    split. apply foo. 
    apply foo0.
  Admitted.
    

Definition uinhabprod : U :=
  csigma cunit (fun x => cunit).

End blaind.
(** Ill formed, not positive *)

Fail Inductive rec := recc : (rec -> unit) -> rec.

Inductive R : Type :=
| ty : F 0 -> R

fix F (n : nat) : Type :=
  R -> unit.

Eval compute in ty.

Module Poly.
  Set Universe Polymorphism.

Inductive Unit : Set :=
    tt : Unit.

Inductive foo : Type :=
| base

fix eval (Γ : foo) : Type :=
       match Γ with
       | base => Unit

       end.

Check eval.

End Poly.