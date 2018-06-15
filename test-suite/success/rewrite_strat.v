Require Import RelationClasses Setoid. 
Require Import List Program.Basics.
Require ZArith.
(** Patterns *)
Module Patterns.
Import ZArith.

Local Open Scope Z.
Lemma addrC (x y : Z) : x + y = y + x.
Proof. Admitted.

Infix "a - b" := (a + -b) (at level 80).
Lemma addNKr x y : x + (- x + y) = y.
Proof. Admitted.

(** [rew c] infers the pattern from the left-hand side of c 
  and rewrites all occurrences of the first instance of c.
  The subterm selected has hence to pass the syntactic filtering
  test of the pattern _and_ the unification (using full conversion)
  with the lhs. 

  The syntax for rewriting with a lemma c allows the following switches:
  - "<-" for right-to-left
  - "fi:" for the first instance only (default is all instances of the lhs)
  - "ipat:" for inferrence of the pattern, otherwise no pattern is used (only 
   unification)

*)

Tactic Notation "rew" uconstr(c) :=
  rewrite_strat inorder (fi:ipat:c).

Tactic Notation "rew" "<-" uconstr(c) :=
  rewrite_strat inorder (<- fi:ipat:c).

(** This variant expects the pattern to be given explicitely 
    Not working yet, rewstrategy(s) argument not handled correctly,
   neither is constr_pattern(p) 
*)
(* Tactic Notation "rew" "[" uconstr(p) "]" uconstr(c) := *)
(*   rewrite_strat inorder (pattern p; fi:c). *)

(* Tactic Notation "rewwith" rewstrategy(s) uconstr(c) := *)
(*   rewrite_strat inorder s. *)

Lemma example1 a b c d :
  a + (b * c - a) + d = b * c + d.
Proof.
  rew addrC.
  change (d + (a + (b * c - a)) = b * c + d).
  rew <- addrC.
  change (a + (b * c - a) + d = b * c + d).
  rewrite_strat inorder (pattern (_ - a); fi:addrC).
  change (a + (-a + b * c) + d = b * c + d).
  now rew addNKr.
Qed.


Import List Program.Basics.
Lemma map_comp {A B C} (f : A -> B) (g : B -> C) (l : list A) : map (compose g f) l = map g (map f l).
Proof. Admitted.

Axiom iota : nat -> nat -> list nat.

Definition graph (f : nat -> nat) n := map f (iota 0 n).

Lemma example2 f g n : graph (compose f g) n = graph g (S n).
Proof.
  Fail rewrite map_comp.
  Time rewrite_strat inorder (pattern (graph _ n); fi:map_comp). (* 0.006 *)
  change (map f (map g (iota 0 n)) = graph g (S n)).
Admitted.

Lemma example2' f g n : graph (compose f g) n = graph g (S n).
Proof.
  Fail rewrite map_comp.
  Time rewrite_strat topdown fi:map_comp. (* 0.026 No pattern, using full conversion *)
  Undo.
  Time rewrite_strat inorder fi:map_comp. (* 0.012 No pattern, using full conversion *)
  change (map f (map g (iota 0 n)) = graph g (S n)).
Admitted.

(* Close Scope Z. *)
Local Open Scope nat.

Lemma addnA n m p : n + (m + p) = n + m + p.
Admitted.

Lemma example3 n m : n + 2 * m = m + (m + n).
Proof.
  rewrite addnA. (* No conversion *)
  Undo.
  Time rewrite_strat topdown fi:addnA. (* 0.029 With conversion, find n + (m + (m + 0)) *)
  change (n + m + (m + 0) = m + (m + n)).
  Undo 2.
  Time rewrite_strat inorder fi:addnA. (* 0.009 With conversion, find n + (m + (m + 0)) *)
  change (n + m + (m + 0) = m + (m + n)).
  Undo 2.
  Time rewrite_strat inorder fi:ipat:addnA. (* 0.008 With pattern matching guard m + m + n *)
  change (n + 2 * m = m + m + n).
  now rewrite Nat.add_comm, !Nat.mul_succ_l.
Qed.

Import Nat.

Example allinsts m : 1 + m = 1 + (0 + m).
Proof.
  Time rew add_1_l.
  easy.
Defined.

Structure Monoid :=
  { A : Type;
    monop : A -> A -> A; mon_unit : A; monunitl : forall x, monop mon_unit x = x }.

Canonical Structure monoid_nat : Monoid :=
  {| monop := add; mon_unit := 0; monunitl := add_0_l |}.

Lemma montest n : 0 + n = n.
Proof.
  (* Fail rewrite monunitl. *)
  rewrite_strat inorder (fi:ipat:monunitl).
  easy.
Qed.

(* Should it work in a two-way fashion? 
  Currently only when no patterns are given.
*)
Lemma montest' (n : nat) : monop _ (mon_unit _) n = n.
Proof.
  (* Fail rewrite monunitl. *)
  rewrite_strat inorder (fi:add_0_l).
  easy.
Qed.


(* Fail Eval compute in pow 2 100. *)

Lemma examplehuge x : pow 2 100 + x * (1 - 1) = 0.
Proof.
  rewrite <- mult_n_O. Undo.
Set Keyed Unification.
  rewrite <- mult_n_O.
  Undo.
Unset Keyed Unification.
rewrite_strat inorder (<- fi:mult_n_O).
Undo.
Set Keyed Unification.
Time rewrite_strat topdown (pattern (_ * _); <- fi:mult_n_O). (* 0.08 *)
Undo.
Time rewrite_strat inorder (pattern (_ * _); <- fi:mult_n_O).
(* 0.033 With pattern matching guard (_ * _) *)
change (Init.Nat.add (pow 2 100) 0 = 0).
(* Fast due to inferred pattern guard *)
rewrite_strat inorder (<- fi:ipat:plus_n_O).
Admitted.

(** Generalized rewriting with equality *)
Variable X : Set.

Goal forall x y : nat, forall P : nat -> nat, x = y -> P x = P y.
Proof.
  intros.
  rewrite_strat topdown H.
  Show Proof.
  reflexivity.
Qed.

Goal forall x y : nat, forall P : nat -> nat, x = y -> P x = P y.
Proof.
  intros.
  rewrite_strat topdown <- H.
  Show Proof.
  reflexivity.
Qed.

Goal forall x y : nat, forall P : nat -> Prop, x = y -> P x <-> P y.
Proof.
  intros.
  rewrite_strat topdown <- H.
  Show Proof.
  reflexivity.
Qed.

Goal forall x y : nat, forall P : nat -> Prop, x = y -> P x <-> P y.
Proof.
  intros.
  rewrite_strat topdown <- H.
  Show Proof.
  reflexivity.
Qed.

Goal forall x y : nat, forall P : nat -> Prop, x = y -> P x <-> P y.
Proof.
  intros.
  setoid_rewrite <- H.
  Show Proof.
  reflexivity.
Qed.

Goal forall x y : nat, forall P : nat -> Prop, x+0 = x -> P (x+0) <-> P x.
Proof.
  intros.
  setoid_rewrite H.
  Show Proof.
  reflexivity.
Qed.

Variable f : X -> X.
Variable g : X -> X -> X.
Variable h : nat -> X -> X.

Variable lem0 : forall x, f (f x) = f x.
Variable lem1 : forall x, g x x = f x.
Variable lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Variable lem3 : forall x, h 0 x = x.

Hint Rewrite lem0 lem1 lem2 lem3 : rew.

Goal forall x, h 10 x = f x.
Proof. 
  intros.
  Time autorewrite with rew. (* 0.586 *)
  reflexivity.
Time Qed. (* 0.53 *)

Goal forall x, h 6 x = f x.
intros.
  Time rewrite_strat topdown lem2.
Show Proof.
  Time rewrite_strat topdown lem1.
  Time rewrite_strat topdown lem0.
  Time rewrite_strat topdown lem3.
  reflexivity.
Undo 5.
  Time rewrite_strat topdown (choice lem2 lem1).
Show Proof.
  Time rewrite_strat topdown (choice lem0 lem3).
  reflexivity.
Undo 3. 
  Time rewrite_strat (topdown (choice lem2 lem1); topdown (choice lem0 lem3)).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 (choice lem1 (choice lem0 lem3)))). 
  reflexivity.  
Undo 2.
  Time rewrite_strat (topdown (choice lem2 (choice lem1 (choice lem0 lem3)))).
  reflexivity.
  Show Proof.
Qed.

Goal forall x, h 10 x = f x.
Proof. 
  intros. simpl.
  Unset Keyed Unification.
  Time rewrite_strat topdown (hints rew). (* 0.38 *) 
  reflexivity.
Time Qed. (* 0.06 s *)
