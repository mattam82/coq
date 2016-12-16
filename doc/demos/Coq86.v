(** This file introduces the new features of Coq 8.6 *)

From Coq Require Import Arith List Omega Bool Program.Tactics.
  
(** * Fine grained error-reporting and error processing, in structured scripts *)

(* In CoqIDE, Coqoon, PG-XML proof blocks confine errors hence Coq can continue to
   process the structured proof *)

(* Lemma failing_branch : False /\ True. *)
(* Proof. *)
(* split. *)
(*   { exact I. }  (* This branch fails, but Coq does not give up *) *)
(*   { exact I. }  (* This branch is executed, can be edited, etc... *) *)
(* Qed. *)

(* This behavior can be disabled, see "error resiliency" command line flags *)

(** Multi-goal, multi-success typeclasses eauto engine See
    Coq86typeclasses for a more detailed demonstration. *)

Class pred (n : nat) : Prop := {}.
Instance pred0 : pred 0 := {}.
(** pred1 has priority over pred0 *)
Instance pred1 : pred 1 := {}.
Class pred2 (n : nat) : Prop := {}.
(** There is not [pred2 1] instance *)
Instance pred20 : pred2 0 := {}.

Goal exists x : nat, pred x /\ pred2 x.
  eexists. split.
  (** The resolution can backtrack across goals, *)
  Set Typeclasses Debug.
  (** Here using two different calls to resolution on two different
      goals, using the multiple successes of the first call to find
      pred0 *)
  all:[> typeclasses eauto .. ].
  Undo.
  (** Here using a multi-goal call *)
  all:typeclasses eauto.
  Show Proof.  
Qed.

(** Goal selectors *)

Goal exists n : nat, pred n /\ pred2 n /\ True.
  eexists.
  split; [|split].
  (** Applies the multi-goal tactic to the list of goals *)
  1-2:typeclasses eauto.
  exact I.
  Undo 2.
  2-3:cycle 1.
  1,3:typeclasses eauto.
  (* Same result, selection of non-contiguous range *)
  exact I.
Qed.

(** Warnings *)

Set Warnings "all". 
Test Warnings.

(** Turns unknown warning into an error *)
Set Warnings "+unknown-warning". 
Test Warnings.

Fail Set Warnings "bla".

(** Turns it back into a warning *)
Set Warnings "unknown-warning". 
Test Warnings.

Set Warnings "bla".

(** What is the semantics of all,default? *)
Set Warnings "default".
Test Warnings.

Print Warnings.
Print Warnings "numbers".
Print Warnings "numbers":"large-nat".
Set Warnings "+large-nat".
Print Warnings "numbers":"large-nat".

(** Irrefutable patterns *)

Require Vector.

Module IrrefutablePatterns.
  (* Show uses of irrefutable patterns in binders *)

  Definition fst {A B} '((a, b) : _ * B) : A := a.
  Definition snd {A B} '((a, b) : A * B) := b.

  Definition swap {A B} '((x,y) : A*B) := (y,x).
  Print swap.
  
  (** The syntax is actually for any destructive patterns, not only for pairs *)

  Record myrec := makemy { somebool : bool; somenat : nat }.
         
  Lemma eta_my : forall '(makemy b n), b = true \/ b = false.
    intros [[|] n]; auto.
  Qed.

  Definition proj_informative A P '(exist _ x _ : { x:A | P x }) : A := x.
  Print proj_informative.

  (* Binding a pair, without explicit type *)

  Definition sum '(x,y) := x+y.
  Print sum.

  (* Using pairs in "fun" and "forall" *)

  Check fun (A B:Type) '((x,y) : A*B) => swap (x,y) = (y,x).
  Check forall (A B:Type) '((x,y) : A*B), swap (x,y) = (y,x).

  (* Using pairs in arbitrary notations supporting binders *)

  Check exists A '((x,y):A*A), swap (x,y) = (y,x).
  Check exists A '((x,y):A*A) '(z,w), swap (x,y) = (z,w).

  Inductive Foo := Bar : nat -> bool -> unit -> nat -> Foo.
  Definition foo '(Bar n b tt p) := if b then n+p else n-p.
  Print foo.

  Definition baz '(Bar n1 b1 tt p1) '(Bar n2 b2 tt p2) := n1+p1.
  Print baz.

  (** Irrefutable patterns can also be used for pattern-matching on a
      type with several constructors when only one of them is possible *)

  Import Vector VectorDef.VectorNotations.
  Definition hd A n '(a::v : Vector.t  A (S n)) := a.

End IrrefutablePatterns.

(** Ltacprof *)

(** Cleaner generic arguments *)

Module GenericArguments.

End GenericArguments.

(** Keyed Unification *)

Module KeyedUnification.
  (** The purpose of Keyed Unification is to allow [rewrite] to see subterms to rewrite
      up to controlable reduction. The strategy is to match the lhs or rhs of the lemma 
      with a subterm in the goal or hypothesis, by finding an applicative subterm whose
      head is equivalent to the head in the lemma and the use full unification on the 
      arguments, whether they are closed or not. *)
  Set Keyed Unification.
  
  Section foo.
    Variable f : nat -> nat. 
    
    Definition g := f.
    
    Variable lem : g 0 = 0.
    
    Goal f 0 = 0.
    Proof.
      Fail rewrite lem.
      (** Found no subterm matching "g 0" in the current goal. *)
    Abort.

    Declare Equivalent Keys @g @f.
    (** Now f and g are considered equivalent heads for subterm selection *)
    Goal f 0 = 0.
    Proof.
      rewrite lem.
      reflexivity.
    Qed.
    
    Print Equivalent Keys.
  End foo.
End KeyedUnification.
  
(** Unification constraint handling *)

Module UnifConstraints.

  (** This option governs the automating solving of remaining unification constraints
      at each ".". Unification can use heuristics to solve these remaining constraints. *)
  Set Solve Unification Constraints. (* The default *)
  
  Goal forall n : nat, True /\ True /\ True \/ n = n.
    (** This higher-order unification constraint does not have a unique solution. *)
    intros n. Fail refine (nat_rect _ _ _ n).
    Unset Solve Unification Constraints.
    (** This lets the constraint float. *)
    refine (nat_rect _ _ _ n).
    (** This forces constraint solving, here failing *)
    Fail solve_constraints.
    (** If we remove the spurious dependency of the predicate on [n]: *)
    Undo 2.
    simple refine (nat_rect _ _ _ n). (* simple refine does not shelve dependent subgoals *)
    Set Printing Existential Instances.
    clear n. intros n. (* We must use an intro here to let the unifier solve 
                          the higher-order problem *)
    solve_constraints.
    all:simpl.
  Admitted.
End UnifConstraints.

(** Compatibility options *)

(** The options to make code compatible with Coq 8.5 are the following 
  (loaded by -compat 8.5).
*)

(** We use some deprecated options in this file, so we disable the
    corresponding warning, to silence the build of this file. *)
Local Set Warnings "-deprecated-option".

(** Subst has some irregularities *)

Global Unset Regular Subst Tactic.

(** [abstract]ed proofs and Program obligations were not shrinked.
  Shrinking removes abstractions by unused variables in these cases *)
Global Unset Shrink Abstract.
Global Unset Shrink Obligations.

(** Refolding was used not only by [cbn] but also during unification,
  resulting in blowups sometimes. *)
Global Set Refolding Reduction.

(** The resolution algorithm for type classes has changed. *)
Global Set Typeclasses Legacy Resolution.

(** The resolution algorithm tried to limit introductions (and hence
  eta-expansions). Can be very expensive as well *)
Global Set Typeclasses Limit Intros.

(** The unification strategy for typeclasses eauto has changed, 
  Filtered Unification is not on by default in 8.6 though. *)
Global Unset Typeclasses Filtered Unification.

(** Allow silently letting unification constraints float after a ".", now
  disallowed by default (one gets unification errors instead) *)
Global Unset Solve Unification Constraints.

(** Experimental features *)

(** This makes "injection" leaving new hypotheses in the context,
  consistently with what "induction" and "destruct" do. Additionally,
  it generates the hypotheses in the natural left-to-right order
  rather than right-to-left order and it clears the original hypothesis.
  Otherwise said, the flag makes "injection" works as "injection as".
*)

Global Set Structural Injection.
Goal forall x y, (x,y)=(0,0) -> True.
intros * H.
injection H.
Abort.

Module Notations.
  (* Recursive notations for binders can now be combined with
     recursive notations for terms *)

  Inductive ftele : Type :=
  | fb {T:Type} : T -> ftele
  | fr {T} : (T -> ftele) -> ftele.

  Fixpoint args ftele : Type :=
    match ftele with
      | fb _ => unit
      | fr f => sigT (fun t => args (f t))
    end.

  Definition fpack := sigT args.
  Definition pack fp fa : fpack := existT _ fp fa.

  Notation "'telescope' x .. z := b" :=
    (fun x => .. (fun z =>
                    pack (fr (fun x => .. ( fr (fun z => fb b) ) .. ) )
                         (existT _ x .. (existT _ z tt) .. )
                 ) ..)
      (at level 85, x binder, z binder).

  Check telescope (t:Type) '((y,z):nat*nat) (x:t) := tt.

End Notations.

Module Contradiction.
  (* "contradiction", hence "easy" now solves intuitively contradictory
  goals negating a trivially true formula ("True", "unit", "t=t", etc. *)

  Goal ~True -> 0=1.
  intros.
  contradiction.
  Qed.

  Goal 0<>0 -> 0=1.
  easy.
  Qed.

End Contradiction.

Module IntroductionPatterns.

  Module TupleIntroductionPatterns.
    (* Tuples pattern must now combine as many patterns as there are
       arguments to the corresponding constructor *)

    Goal (exists x, x = 0) -> True.
    Fail intros (x).
    intros (x,Hx).
    Abort.

    (* Former code which does not comply to this invariant is expected
       to be upgraded *)

  End TupleIntroductionPatterns.

  Module BracketingLastIntroductionPattern.
    (* The last disjunctive/conjunctive introduction pattern of a
       sequence now behaves as if it were not the last of the sequence,
       padding with enough names to ensure well-bracketing and
       composability. *)

    Goal forall A B C D, A \/ B -> C /\ D -> A /\ C \/ B /\ D.
    intros * [|]; intros (HC,HD).
    Undo.

    (* The 8.5 behavior can be recovered with the following option *)

    Global Unset Bracketing Last Introduction Pattern.

    (* In 8.5, "intros [|]", taken e.g. on a goal "A\/B->...", does not
       behave as "intros [H|H]" but leave instead hypotheses quantified in
       the goal, here producing subgoals A->... and B->... *)

    intros * [|]. Fail intros (HC,HD).
    Abort.

  End BracketingLastIntroductionPattern.

End IntroductionPatterns.
