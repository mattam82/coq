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
