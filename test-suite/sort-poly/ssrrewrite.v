From Coq Require Import ssreflect.
Set SsrRewrite.

(* Ssreflect's rewrite looks still totally bugged *)


(* Definition foo1@{s| |} (A B :Type@{s|Set}) (e : eq@{Type s|_} A B) : A -> B. *)
(* Proof. *)
(*   rewrite e; trivial. *)
(* Fail Defined. *)

(* Definition foo2@{s|u |} (A :Type@{s|Set}) {x y : A} (P : A -> Type@{s|u}) (e : x ≡ y) : P x -> P y. *)
(* Proof. *)
(*   Set Printing Universes. *)
(*   Set Printing All. *)
(*   rewrite e. *)
(*   trivial. *)
(* Defined. *)

(* Definition foo3@{s s'|u |} (A :Type@{s|Set}) {x y : A} (P : A -> Type@{s'|u}) (e : x = y :> A) : P x -> P y. *)
(* Proof. *)
(*   Set Printing Universes. *)
(*   Set Printing All. *)
(*   rewrite e. *)
(*   trivial. *)
(* Defined. *)

(* Definition foo4@{s| |} (A B :Type@{s|Set}) (e : A = B :> Type@{s|Set+1}) : A -> B. *)
(* Proof. *)
(*   rewrite e. *)
(*   trivial. *)
(* Fail Defined. (* minimization problem *) *)
(*   Show Proof. *)
(* Qed. *)
