(* (* What's going on? *) *)
(* (* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "src" "Crypto" "-R" "Bedrock"  *)
(* "Bedrock" "-R" "coqprime/Coqprime" "Coqprime" "-top" "NewBaseSystemLetInMonad")  *)
(* -*- *) *)
(* (* File reduced by coq-bug-finder from original input, then from 619 lines to  *)
(* 61 lines, then from 210 lines to 101 lines, then from 203 lines to 103 lines,  *)
(* then from 217 lines to 107 lines, then from 299 lines to 121 lines, then from  *)
(* 170 lines to 121 lines, then from 135 lines to 121 lines *) *)
(* (* coqc version 8.6rc1 (December 2016) compiled on Dec 8 2016 13:43:59 with  *)
(* OCaml 4.02.3 *)
(*    coqtop version 8.6rc1 (December 2016) *) *)
(* Axiom proof_admitted : False. *)
(* Tactic Notation "admit" := abstract case proof_admitted. *)
(* Require Coq.ZArith.ZArith. *)

(* Global Set Asymmetric Patterns. *)
(* Import Coq.ZArith.BinInt. *)

(* Class Decidable (P : Prop) := dec : {P} + {~P}. *)
(* Arguments dec _%type_scope {_}. *)

(* Notation DecidableRel R := (forall x y, Decidable (R x y)). *)
(* Global Instance dec_eq_prod {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)}  *)
(* : DecidableRel (@eq (A * B)) | 10. *)
(* admit. *)
(* Defined. *)

(* Global Instance dec_eq_Z : DecidableRel (@eq Z) | 10 := Z.eq_dec. *)
(* Global Instance dec_le_Z : DecidableRel BinInt.Z.le := ZArith_dec.Z_le_dec. *)
(* Global Instance dec_ge_Z : DecidableRel BinInt.Z.ge := ZArith_dec.Z_ge_dec. *)

(* Reserved Notation "A <- X ; B" (at level 70, right associativity, format "'[v'  *)
(* A  <-  X ; '/' B ']'"). *)
(* Reserved Notation "'mlet' x := A 'in' b" *)
(*          (at level 200, b at level 200, format "'mlet'  x  :=  A  'in' '//' b"). *)

(* Reserved Notation "'dlet' x := y 'in' f" *)
(*          (at level 200, f at level 200, format "'dlet'  x  :=  y  'in' '//' f"). *)

(* Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in  *)
(* f y. *)
(* Notation "'dlet' x := y 'in' f" := (Let_In y (fun x => f)). *)
(* Local Set Universe Polymorphism. *)

(* Inductive LetInM : Type -> Type := *)
(* | ret {T} (v : T) : LetInM T *)
(* | let_in {A B} (v : A) (f : A -> LetInM B) : LetInM B. *)
(* Delimit Scope letinm_scope with letinm. *)
(* Notation "'mlet' x := y 'in' f" := (let_in y (fun x => f%letinm)) :  *)
(* letinm_scope. *)

(* Fixpoint denote {A} (x : LetInM A) : A := *)
(*   match x with *)
(*   | ret _ v => v *)
(*   | let_in T A v f => dlet x := v in @denote A (f x) *)
(*   end. *)

(* Fixpoint bind {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B *)
(*   := match v in LetInM A return (A -> _) -> _ with *)
(*      | ret T v => fun f => f v *)
(*      | let_in A B v g => fun f => let_in v (fun x => bind (g x) f) *)
(*      end. *)
(* Notation "x <- y ; z" := (bind y%letinm (fun x => z%letinm)) : letinm_scope. *)

(* Fixpoint under_lets {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B *)
(*   := match v in LetInM A return (A -> _) -> _ with *)
(*      | ret T v => fun f => f v *)
(*      | let_in A B v g => fun f => let_in v (fun x => bind (g x) f) *)
(*      end. *)

(* Definition lift {A B} (f : A -> B) : LetInM A -> LetInM B *)
(*   := fun x => under_lets x (fun y => ret (f y)). *)

(* Module Import List. *)
(*   Definition cons {A} x := lift (@cons A x). *)
(* Infix "::" := List.cons : letinm_scope. *)

(* Definition pull_prod {A B} : LetInM (A * B) -> LetInM A * LetInM B *)
(*   := fun x => (lift fst x, lift snd x). *)
(* Definition pull_prod2 {A B C} : LetInM (A * B * C) -> LetInM A * LetInM B *  *)
(* LetInM C *)
(*   := Eval simpl in fun x => let x := pull_prod x in (pull_prod (fst x), snd x). *)
(* Local Open Scope Z_scope. *)
(* Local Notation llist A := (LetInM (list A)). *)

(*     Fixpoint remove_first {A} (dec:forall x y:A, {x = y} + {x<>y}) (x:A)  *)
(* (ls:list A) *)
(*       := match ls with *)
(*          | nil => nil *)
(*          | (a :: ls')%list => *)
(*            if (dec x a) then ls' else (a :: remove_first dec x ls')%list *)
(*          end. *)

(*     Definition find_remove_first {A dec} (f:A -> bool) ls : (option A) * list A *)
(*       := match List.find (fun a => f a) ls with *)
(*          | None => (None, ls) *)
(*          | Some a => (Some a, remove_first dec a ls) *)
(*          end. *)
(*   Let limb := (Z*Z)%type. *)

(*     Section Saturated. *)
(*       Context {word_max : Z} {word_max_pos : 1 < word_max} *)
(*               {add : Z -> Z -> Z * Z} *)
(*               {add_correct : forall x y, fst (add x y) + word_max * snd (add x  *)
(* y) = x + y} *)
(*               {end_wt:Z} {end_wt_pos : 0 < end_wt} *)
(*       . *)

(*       Polymorphic Definition has_same_wt (cx:limb) := fun a:limb => if dec (fst cx = fst a)  *)
(* then true else false. *)
(*       Require Import Recdef. *)

(*       Function add_and_carry (cx:limb) (acc p:llist limb) *)
(*                {measure (fun cx => Z.to_nat (end_wt - fst cx)) cx} *)
(*         : llist limb * llist limb * limb := *)
(*         if dec (fst cx <= 0) then (acc,p,cx) else *)
(*         if dec (fst cx >= end_wt) then (acc, p, cx) else *)
(*           let '(acc, p, cx) := *)
(*               pull_prod2 *)
(*             (under_lets *)
(*                p *)
(*                (fun p => *)
(*           match (@find_remove_first limb dec_eq_prod (has_same_wt cx) p) with *)
(*           | (None,_) => mlet cx' := cx in *)
(*                         let '(acc, p, cx) := add_and_carry (fst cx * word_max,  *)
(* 0) (cx :: acc)%letinm (ret p) in *)
(*                         acc <- acc; *)
(*                         p <- p; *)
(*                        ret (acc, p, cx) *)
(*           | (Some cx',p') => *)
(*             let '(sum, carry) := add (snd cx) (snd cx') in *)
(*             mlet fst_cx := fst cx in *)
(*             let new_list := ((fst_cx, sum) :: ret p')%letinm in *)
(*             let new_limb := (fst_cx * word_max, carry) in *)
(*             let '(acc, p, cx) := add_and_carry new_limb acc new_list in *)
(*             acc <- acc; *)
(*             p <- p; *)
(*             ret (acc, p, cx) *)
(*           end)%letinm) in *)
(*       (acc, p, denote cx). *)

(* Error: Undeclared universe: Set *)
(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "src" "Crypto" "-R" "Bedrock" 
"Bedrock" "-R" "coqprime/Coqprime" "Coqprime" "-top" "NewBaseSystemLetInMonad") 
-*- *)
(* File reduced by coq-bug-finder from original input, then from 619 lines to 
61 lines, then from 210 lines to 101 lines, then from 203 lines to 103 lines, 
then from 217 lines to 107 lines, then from 299 lines to 121 lines, then from 
170 lines to 121 lines, then from 135 lines to 121 lines, then from 118 lines 
to 57 lines, then from 71 lines to 57 lines *)
(* coqc version 8.6rc1 (December 2016) compiled on Dec 8 2016 13:43:59 with 
OCaml 4.02.3
   coqtop version 8.6rc1 (December 2016) *)
Require Coq.ZArith.ZArith.

Global Set Asymmetric Patterns.
Import Coq.ZArith.BinInt.

Reserved Notation "A <- X ; B" (at level 70, right associativity, format "'[v' 
A  <-  X ; '/' B ']'").

Reserved Notation "'dlet' x := y 'in' f"
         (at level 200, f at level 200, format "'dlet'  x  :=  y  'in' '//' f").

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in 
f y.
Notation "'dlet' x := y 'in' f" := (Let_In y (fun x => f)).
Local Set Universe Polymorphism.

Inductive LetInM : Type -> Type :=
| ret {T} (v : T) : LetInM T
| let_in {A B} (v : A) (f : A -> LetInM B) : LetInM B.
Delimit Scope letinm_scope with letinm.

Fixpoint denote {A} (x : LetInM A) : A :=
  match x with
  | ret _ v => v
  | let_in T A v f => dlet x := v in @denote A (f x)
  end.

Fixpoint bind {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B
  := match v in LetInM A return (A -> _) -> _ with
     | ret T v => fun f => f v
     | let_in A B v g => fun f => let_in v (fun x => bind (g x) f)
     end.
Notation "x <- y ; z" := (bind y%letinm (fun x => z%letinm)) : letinm_scope.

Fixpoint under_lets {A B} (v : LetInM A) : forall (f : A -> LetInM B), LetInM B
  := match v in LetInM A return (A -> _) -> _ with
     | ret T v => fun f => f v
     | let_in A B v g => fun f => let_in v (fun x => bind (g x) f)
     end.

Definition lift {A B} (f : A -> B) : LetInM A -> LetInM B
  := fun x => under_lets x (fun y => ret (f y)).
Definition pull_prod {A B} : LetInM (A * B) -> LetInM A * LetInM B
  := fun x => (lift fst x, lift snd x).
Local Notation llist A := (LetInM (list A)).
Axiom admit : forall {T}, T.

Variable end_wt : Z.
Require Import Recdef.
Function add_and_carry (cx : Z*Z)
         {measure (fun cx => Z.to_nat (end_wt - fst cx)) cx}
  : llist (Z*Z)%type * (Z*Z) :=
  let '(p, cx) :=
      pull_prod
        ((let '(p, cx) := add_and_carry admit in
          p <- p;
            ret (p, cx)
         )%letinm) in
  (p, denote cx).
apply admit. Set Printing All. Set Printing Universes.
Defined.