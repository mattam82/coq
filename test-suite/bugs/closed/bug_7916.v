From Coq Require Import Setoid.

Lemma test {A}
      (lookup : list A -> nat -> option A)
      (opA : option A -> option A -> option A)
      (opL : list A -> list A -> list A)
      (val : option A -> Prop) :
   (forall l1 l2 (i : nat), lookup (opL l1 l2) i = opA (lookup l1 i) (lookup l2 i)) ->
   forall l1 l2, (forall i : nat, val (lookup (opL l1 l2) i)) -> forall i : nat, val (lookup l1 i).
Proof.
  intros list_lookup_op l1 l2.
  (* setoid_rewrite list_lookup_op. Undo. *)
Hint Mode Reflexive ! ! : typeclass_instances.

  setoid_rewrite list_lookup_op.
Abort.

(* Minimized bug from math-comp*)
Module MathComp.

(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "seq") -*- *)
(* File reduced by coq-bug-finder from original input, then from 4170 lines to 77 lines, then from 96 lines to 1135 lines, then from 1139 lines to 101 lines, then from 119 lines to 516 lines, then from 520 lines to 108 lines, then from 123 lines to 158 lines, then from 162 lines to 108 lines, then from 121 lines to 253 lines, then from 257 lines to 109 lines, then from 113 lines to 109 lines *)
(* coqc version 8.14+alpha compiled with OCaml 4.12.0
   coqtop version 8.14+alpha *)
   Axiom proof_admitted : False.
   Tactic Notation "admit" := abstract case proof_admitted.
   Require Coq.ssr.ssreflect.

   Export Coq.ssr.ssreflect.
   Global Set Asymmetric Patterns.
   Require Coq.ssr.ssrbool.
   Require Coq.NArith.BinNat.
   Export Coq.ssr.ssrfun.
   Export Coq.ssr.ssrbool.

   Definition PredType : forall T pT, (pT -> pred T) -> predType T.
   exact PredType || exact mkPredType.
   Defined.
   Arguments PredType [T pT] toP.

   Set Implicit Arguments.
   Unset Strict Implicit.

   Module Export Equality.

   Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

   Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
   Notation class_of := mixin_of (only parsing).

   Section ClassDef.

   Structure type := Pack {sort; _ : class_of sort}.
   Local Coercion sort : type >-> Sortclass.
   Variables (T : Type) (cT : type).

   Definition class := let: Pack _ c := cT return class_of cT in c.

   End ClassDef.
   Coercion sort : type >-> Sortclass.
   Notation eqType := type.

   Definition eq_op T := Equality.op (Equality.class T).

   Notation "x == y" := (eq_op x y)
     (at level 70, no associativity) : bool_scope.
   Notation xpredU1 := (fun a1 (p : pred _) x => (x == a1) || p x).

   Declare Scope seq_scope.
   Open Scope seq_scope.

   Notation seq := list.

   Infix "::" := cons : seq_scope.

   Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

   Section Sequences.

   Variable T : Type.
   Implicit Type s : seq T.

   Definition behead s := if s is _ :: s' then s' else [::].

   End Sequences.

   Section EqSeq.

   Variables (n0 : nat) (T : eqType) (x0 : T).

   Fixpoint mem_seq (s : seq T) :=
     if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

   Definition seq_eqclass := seq T.
   Coercion pred_of_seq (s : seq_eqclass) : {pred T} := mem_seq s.

   Canonical seq_predType := PredType (pred_of_seq : seq T -> pred T).

   Lemma mem_head x s : x \in x :: s.
   admit.
   Defined.

   Lemma mem_behead s : {subset behead s <= s}.
   admit.
   Defined.

   Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

   End EqSeq.

   Section Map.

   Variables (n0 : nat) (T1 : Type) (x1 : T1).
   Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

   Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

   End Map.

   Variables (n0 : nat) (T1 : eqType) (x1 : T1).
   Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).

   Lemma mapP s y : reflect (exists2 x, x \in s & y = f x) (y \in map f s).
   admit.
   Defined.

   Lemma map_inj_in_uniq s : {in s &, injective f} -> uniq (map f s) = uniq s.
   Proof.
   elim: s => //= x s IHs //= injf; congr (~~ _ && _).
     apply/mapP/idP=> [[y sy /injf] | ]; last by exists x.
    rewrite mem_head.
    rewrite mem_behead // => -> //.
   Abort.
  End Equality.
End MathComp.

Module Iris.
(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/prelude" "iris.prelude" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/algebra" "iris.algebra" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/si_logic" "iris.si_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/bi" "iris.bi" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/proofmode" "iris.proofmode" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/base_logic" "iris.base_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/program_logic" "iris.program_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_staging" "iris.staging" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "ofe") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1726 lines to 63 lines, then from 117 lines to 133 lines, then from 137 lines to 64 lines, then from 115 lines to 134 lines, then from 138 lines to 69 lines, then from 96 lines to 750 lines, then from 752 lines to 101 lines, then from 126 lines to 357 lines, then from 361 lines to 116 lines, then from 140 lines to 190 lines, then from 194 lines to 125 lines, then from 148 lines to 1547 lines, then from 1547 lines to 152 lines, then from 156 lines to 152 lines *)
(* coqc version 8.14+alpha compiled with OCaml 4.12.0
   coqtop version 8.14+alpha *)
   Axiom proof_admitted : False.
   Tactic Notation "admit" := abstract case proof_admitted.
   Require Coq.ssr.ssreflect.
   Require Coq.Lists.List.
   Require Coq.Unicode.Utf8.
   Module Export stdpp_DOT_base.
   Module Export stdpp.
   Module Export base.
   Export Coq.Classes.Morphisms.
   Export Coq.Setoids.Setoid.
   Export Coq.Unicode.Utf8.

   Global Generalizable All Variables.

   Declare Scope stdpp_scope.
   Global Open Scope stdpp_scope.

   Notation "(=)" := eq (only parsing) : stdpp_scope.
   Notation "(=@{ A } )" := (@eq A) (only parsing) : stdpp_scope.

   Class Equiv A := equiv: relation A.

   Infix "≡" := equiv (at level 70, no associativity) : stdpp_scope.

   Class Decision (P : Prop) := decide : {P} + {¬P}.
   Global Arguments decide _ {_} : simpl never, assert.

   Class RelDecision {A B} (R : A → B → Prop) :=
     decide_rel x y :> Decision (R x y).
   Notation EqDecision A := (RelDecision (=@{A})).

   Class Inj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
     inj x y : S (f x) (f y) → R x y.

   Lemma not_symmetry `{R : relation A, !Symmetric R} x y : ¬R x y → ¬R y x.
   admit.
   Defined.
   End base.

   End stdpp.

   End stdpp_DOT_base.
   Module Export stdpp_DOT_decidable.
   Module Export stdpp.
   Module Export decidable.
   Notation cast_if S := (if S then left _ else right _).

   Program Definition inj_eq_dec `{EqDecision A} {B} (f : B → A)
     `{!Inj (=) (=) f} : EqDecision B := λ x y, cast_if (decide (f x = f y)).
   Solve Obligations with firstorder congruence.

   End decidable.

   End stdpp.

   End stdpp_DOT_decidable.
   Module Export stdpp_DOT_tactics.
   Module Export stdpp.
   Module Export tactics.

   Ltac fast_done :=
     solve
       [ eassumption
       | symmetry; eassumption
       | apply not_symmetry; eassumption
       | reflexivity ].

   Ltac done :=
     solve
     [ repeat first
       [ fast_done
       | solve [trivial]

       | progress intros
       | solve [symmetry; trivial]
       | solve [apply not_symmetry; trivial]
       | discriminate
       | contradiction
       | split
       | match goal with H : ¬_ |- _ => case H; clear H; fast_done end ]
     ].

   End tactics.

   End stdpp.

   End stdpp_DOT_tactics.
   Module Export stdpp.
   Module Export prelude.
   Export stdpp.tactics.

   End prelude.
   Export Coq.ssr.ssreflect.
   Export stdpp.prelude.
   Set Primitive Projections.

   Class Dist A := dist : nat → relation A.
   Notation "x ≡{ n }≡ y" := (dist n x y)
     (at level 70, n at next level, format "x  ≡{ n }≡  y").
   Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).

   Record OfeMixin A `{Equiv A, Dist A} := {
     mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
     mixin_dist_equivalence n : Equivalence (@dist A _ n);
     mixin_dist_S n (x y : A) : x ≡{S n}≡ y → x ≡{n}≡ y
   }.

   Structure ofe := Ofe {
     ofe_car :> Type;
     ofe_equiv : Equiv ofe_car;
     ofe_dist : Dist ofe_car;
     ofe_mixin : OfeMixin ofe_car
   }.
   Global Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _) : typeclass_instances.
   Global Hint Extern 0 (Dist _) => eapply (@ofe_dist _) : typeclass_instances.

   Section ofe_mixin.
     Context {A : ofe}.
     Implicit Types x y : A.
     Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y.
   admit.
   Defined.
     Global Instance dist_equivalence n : Equivalence (@dist A _ n).
   admit.
   Defined.
   End ofe_mixin.

   Record chain (A : ofe) := {
     chain_car :> nat → A;
     chain_cauchy n i : n ≤ i → chain_car i ≡{n}≡ chain_car n
   }.

   Program Definition chain_map {A B : ofe} (f : A → B)
       `{!NonExpansive f} (c : chain A) : chain B :=
     {| chain_car n := f (c n) |}.
   Next Obligation.
   admit.
   Defined.

   Notation Compl A := (chain A%type → A).
   Class Cofe (A : ofe) := {
     compl : Compl A;
     conv_compl n c : compl c ≡{n}≡ c n;
   }.

   Lemma compl_chain_map `{Cofe A, Cofe B} (f : A → B) c `(NonExpansive f) :
     compl (chain_map f c) ≡ f (compl c).
   Proof.
   apply equiv_dist=>n.
   rewrite !conv_compl.
   Abort.
   End stdpp.
End Iris.

(*Module Equations.
(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/theories" "Equations" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/examples" "Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/src" "-top" "AlmostFull") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1462 lines to 81 lines, then from 125 lines to 247 lines, then from 251 lines to 84 lines, then from 124 lines to 359 lines, then from 363 lines to 84 lines, then from 124 lines to 176 lines, then from 180 lines to 84 lines, then from 124 lines to 297 lines, then from 300 lines to 84 lines, then from 88 lines to 84 lines *)
(* coqc version 8.14+alpha compiled with OCaml 4.05.0
   coqtop version 8.14+alpha *)
   Axiom proof_admitted : False.
   Tactic Notation "admit" := abstract case proof_admitted.
   Require Equations.Prop.Equations.
   Require Coq.Unicode.Utf8.
   Require Coq.micromega.Lia.
   Require Coq.ssr.ssreflect.

   Inductive fin : nat -> Set :=
   | fz : forall {n}, fin (S n)
   | fs : forall {n}, fin n -> fin (S n).

   Import Equations.Prop.Equations.
   Import Coq.Relations.Relations.
   Import Coq.Unicode.Utf8.
   Import Coq.Classes.Morphisms.
   Import Coq.Arith.Arith.

   Section AlmostFull.
     Context {X : Type}.

     Inductive WFT : Type :=
     | ZT : WFT
     | SUP : (X -> WFT) -> WFT.

     Fixpoint SecureBy (R : X -> X -> Prop) (p : WFT) : Prop :=
       match p with
       | ZT => forall x y, R x y
       | SUP f => forall x, SecureBy (fun y z => R y z \/ R x y) (f x)
       end.

     Definition almost_full (R : X -> X -> Prop) := exists p, SecureBy R p.

   End AlmostFull.

   Class AlmostFull {X} (R : X -> X -> Prop) :=
     is_almost_full : almost_full R.

   #[export] Instance proper_af X : Proper (relation_equivalence ==> iff) (@AlmostFull X).
   admit.
   Defined.
   Import Coq.ssr.ssreflect.

     Definition subgraph k k' := fin k -> option (bool * fin k').
     Definition graph k := subgraph k k.

     Equations k_tuple_type (k : nat) : Type :=
     k_tuple_type 0 := unit;
     k_tuple_type (S n) := nat * k_tuple_type n.

     Equations k_tuple_val {k : nat} (f : fin k) (t : k_tuple_type k) : nat :=
       k_tuple_val fz (x, _) := x;
       k_tuple_val (fs f) (_, t) := k_tuple_val f t.

     Equations k_related (k k' : nat) (G : subgraph k k') : k_tuple_type k -> k_tuple_type k' -> Prop :=
       k_related 0 k' g := fun _ _ => True;
       k_related (S k) k' g with g fz :=
         { | Some (weight, d) := fun x y =>
                                   (if weight then k_tuple_val fz x < k_tuple_val d y
                                    else (Peano.le (k_tuple_val fz x) (k_tuple_val d y))) /\
                                   k_related k k' (fun f => g (fs f)) (snd x) y;
           | None => fun _ _ => False }.

     Definition graph_relation {k : nat} (G : graph k) : relation (k_tuple_type k) :=
       k_related k k G.

     Equations TI_graph k : graph k :=
       TI_graph 0 := λ{ | ! } ;
       TI_graph (S n) := fun f => Some (false, f).

     Definition TI k : relation (k_tuple_type k) := graph_relation (TI_graph k).

     Equations intersection k : relation (k_tuple_type k) :=
       intersection 0 := fun x y => True;
       intersection (S n) := fun x y => Nat.le (fst x) (fst y) /\ intersection n (snd x) (snd y).

     Lemma TI_intersection_equiv k : relation_equivalence (TI k) (intersection k).
   admit.
   Defined.

     #[global] Instance TI_AlmostFull k : AlmostFull (TI k).
     Proof.
       rewrite TI_intersection_equiv.*)

Module SSr.

(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fourcolor/theories" "fourcolor" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "realcategorical") -*- *)
(* File reduced by coq-bug-finder from original input, then from 451 lines to 35 lines, then from 99 lines to 1013 lines, then from 1016 lines to 85 lines, then from 99 lines to 206 lines, then from 209 lines to 101 lines, then from 114 lines to 360 lines, then from 363 lines to 185 lines, then from 198 lines to 330 lines, then from 334 lines to 185 lines, then from 189 lines to 185 lines *)
(* coqc version 8.14+alpha compiled with OCaml 4.12.0
   coqtop version 8.14+alpha *)
   Axiom proof_admitted : False.
   Tactic Notation "admit" := abstract case proof_admitted.
   Require Coq.ssr.ssreflect.

   Export Coq.ssr.ssreflect.
   Require Coq.NArith.BinNat.

   Set Implicit Arguments.
   Unset Strict Implicit.

   Module Export Real.

   Record structure : Type := Structure {
      val : Type;
      set := val -> Prop;
      rel := val -> set;
      le : rel;
      sup : set -> val;
      add : val -> val -> val;
      zero : val;
      opp : val -> val;
      mul : val -> val -> val;
      one : val;
      inv : val -> val
   }.

   Definition eq R : rel R := fun x y => le x y /\ le y x.

   Definition ub R (E : set R) : set R := fun z => forall y, E y -> le y z.

   Definition down R (E : set R) : set R := fun x => exists2 y, E y & le x y.

   Definition nonempty R (E : set R) : Prop := exists x, E x.
   Definition has_ub R (E : set R) : Prop := nonempty (ub E).
   Definition has_sup R (E : set R) : Prop := nonempty E /\ has_ub E.

   Record axioms R : Prop := Axioms {
     le_reflexive (x : val R) :
       le x x;
     le_transitive (x y z : val R) :
       le x y -> le y z -> le x z;
     sup_upper_bound (E : set R) :
       has_sup E -> ub E (sup E);
     sup_total (E : set R) (x : val R) :
       has_sup E -> down E x \/ le (sup E) x;
     add_monotone (x y z : val R) :
       le y z -> le (add x y) (add x z);
     add_commutative (x y : val R) :
       eq (add x y) (add y x);
     add_associative (x y z : val R) :
       eq (add x (add y z)) (add (add x y) z);
     add_zero_left (x : val R) :
       eq (add (zero R) x) x;
     add_opposite_right (x : val R) :
       eq (add x (opp x)) (zero R);
     mul_monotone x y z :
       le (zero R) x -> le y z -> le (mul x y) (mul x z);
     mul_commutative (x y : val R) :
       eq (mul x y) (mul y x);
     mul_associative (x y z : val R) :
       eq (mul x (mul y z)) (mul (mul x y) z);
     mul_distributive_right (x y z : val R) :
       eq (mul x (add y z)) (add (mul x y) (mul x z));
     mul_one_left (x : val R) :
       eq (mul (one R) x) x;
     mul_inverse_right (x : val R) :
       ~ eq x (zero R) -> eq (mul x (inv x)) (one R);
     one_nonzero : ~ eq (one R) (zero R)
   }.

   Record model : Type := Model {
     model_structure : structure;
     model_axioms : axioms model_structure
   }.

   Definition image R S (phi : val R -> val S) (E : set R) (y : val S) :=
     exists2 x, E x & eq y (phi x).

   Record morphism R S (phi : val R -> val S) : Prop := Morphism {
     morph_le x y :
      le (phi x) (phi y) <-> le x y;
     morph_sup (E : set R) :
      has_sup E -> eq (phi (sup E)) (sup (image phi E));
     morph_add x y :
      eq (phi (add x y)) (add (phi x) (phi y));
     morph_zero :
      eq (phi (zero R)) (zero S);
     morph_opp x :
      eq (phi (opp x)) (opp (phi x));
     morph_mul x y :
      eq (phi (mul x y)) (mul (phi x) (phi y));
     morph_one :
      eq (phi (one R)) (one S);
     morph_inv x :
      ~ eq x (zero R) -> eq (phi (inv x)) (inv (phi x))
   }.
   Coercion val : structure >-> Sortclass.
   Coercion model_structure : model >-> structure.
   Delimit Scope real_scope with Rval.
   Local Open Scope real_scope.
   Arguments add {R} x%Rval y%Rval : rename, simpl never.

   Reserved Notation "x == y" (at level 70, no associativity).

   Notation "x <= y" := (le x y) : real_scope.
   Notation "x + y" := (add x y) : real_scope.
   Notation "0" := (zero _) : real_scope.

   Notation "x == y" := (eq x y) : real_scope.
   Notation "x >= y" := (y <= x) (only parsing) : real_scope.
   Notation "x < y" := (~ (x >= y)) : real_scope.
   Notation "x <= y <= z" := (x <= y /\ y <= z) : real_scope.
   Import Coq.Classes.Morphisms.

   Section RealLemmas.

   Variable R : Real.model.
   Implicit Types x y z : R.
   Local Notation eqR :=(@Real.eq (Real.model_structure R)) (only parsing).

   Lemma leRR x : x <= x.
   admit.
   Defined.

   Lemma ltRW x y : x < y -> x <= y.
   admit.
   Defined.

   Lemma eqR_refl x : x == x.
   admit.
   Defined.

   Lemma eqR_sym x y : x == y -> y == x.
   admit.
   Defined.

   Lemma eqR_trans x y z : x == y -> y == z -> x == z.
   admit.
   Defined.

   Add Parametric Relation : R eqR
     reflexivity proved by eqR_refl
     symmetry proved by eqR_sym
     transitivity proved by eqR_trans
     as real_equality.

   Instance addR_Proper : Proper (eqR ==> eqR ==> eqR) Real.add.
   admit.
   Defined.

   Lemma add0R x : 0 + x == x.
   admit.
   Defined.

   End RealLemmas.

   Hint Resolve eqR_refl leRR ltRW.

   Existing Instance real_equality.
   Existing Instance addR_Proper.

   Section RealMorph.

   Variables (R S : Real.structure) (phi : R -> S).
   Hypothesis phiP : Real.morphism phi.

   Lemma Rmorph_eq x y : phi x == phi y <-> x == y.
   Proof.
   by rewrite /Real.eq !Real.morph_le.
   Qed.

   End RealMorph.

   Variables (R : Real.structure) (S : Real.model) (phi : R -> S).
   Hypothesis phiP : Real.morphism phi.
   Implicit Types (x y z : R) (E : Real.set R).
   Let phi_eq := Rmorph_eq phiP.
   Let phiD := Real.morph_add phiP.
   Let phi0 := Real.morph_zero phiP.

   Let Radd0 x : 0 + x == x.
   Proof.
   by rewrite -phi_eq phiD phi0 add0R.
   Abort.
  End Real.
End SSr.
