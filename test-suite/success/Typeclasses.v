(* coq-prog-args: ("-async-proofs" "off") *)
Module applydestruct.
  Class Foo (A : Type) :=
    { bar : nat -> A;
      baz  : A -> nat }.
  Local Hint Mode Foo + : typeclass_instances.

  Class C (A : Type).
  Local Hint Mode C + : typeclass_instances.

  Variable fool : forall {A} {F : Foo A} (x : A), C A -> bar 0 = x.
  (* apply leaves non-dependent subgoals of typeclass type
     alone *)
  Goal forall {A} {F : Foo A} (x : A), bar 0 = x.
  Proof.
    intros. apply fool.
    match goal with
      |[ |- C A ] => idtac
    end.
  Abort.

  Variable fooli : forall {A} {F : Foo A} {c : C A} (x : A), bar 0 = x.
  (* apply tries to resolve implicit argument typeclass
     constraints. *)
  Goal forall {A} {F : Foo A} (x : A), bar 0 = x.
  Proof.
    intros.
    Fail apply fooli.
    Fail unshelve eapply fooli; solve [typeclasses eauto].
    eapply fooli.
  Abort.

  (* It applies resolution after unification of the goal *)
  Goal forall {A} {F : Foo A} {C : C A} (x : A), bar 0 = x.
  Proof.
    intros. apply fooli.
  Abort.
    Set Typeclasses Debug Verbosity 2.

  Inductive bazdestr {A} (F : Foo A) : nat -> Prop :=
    | isbas : bazdestr F 1.

  Variable fooinv : forall {A} {F : Foo A} (x : A),
      bazdestr F (baz x).

  (* Destruct applies resolution early, before finding
     occurrences to abstract. *)
  Goal forall {A} {F : Foo A} {C : C A} (x : A), baz x = 0.
  Proof.
    intros. Fail destruct (fooinv _).
    destruct (fooinv x).
  Abort.

  Goal forall {A} {F : Foo A} (x y : A), x = y.
  Proof.
    intros. rewrite <- (fool x). rewrite <- (fool y). reflexivity.
    match goal with
      |[ |- C A ] => idtac
    end.
  Abort.
End applydestruct.

Module onlyclasses.

(* In 8.6 we still allow non-class subgoals *)
  Variable Foo : Type.
  Variable foo : Foo.
  Local Hint Extern 0 Foo => exact foo : typeclass_instances.
  Goal Foo * Foo.
    split. shelve.
    Set Typeclasses Debug.
    typeclasses eauto.
    Unshelve. typeclasses eauto.
  Qed.

  Module RJung.
    Class Foo (x : nat).
      
      Instance foo x : x = 2 -> Foo x := {}.
      Local Hint Extern 0 (_ = _) => reflexivity : typeclass_instances.
      Typeclasses eauto := debug.
      Check (_ : Foo 2).


      Fail Definition foo := (_ : 0 = 0).

  End RJung.
End onlyclasses.

Module shelve_non_class_subgoals.
  Variable Foo : Type.
  Variable foo : Foo.
  Local Hint Extern 0 Foo => exact foo : typeclass_instances.
  Class Bar := {}.
  Instance bar1 (f:Foo) : Bar := {}.

  Typeclasses eauto := debug.
  Set Typeclasses Debug Verbosity 2.
  Goal Bar.
    (* Solution has shelved subgoals (of non typeclass type) *)
    typeclasses eauto.
  Abort.
End shelve_non_class_subgoals.

Module RefineVsNoTceauto.

  Class Foo (A : Type) := foo : A.
  Instance: Foo nat := { foo := 0 }.
  Instance: Foo nat := { foo := 42 }.
  Local Hint Extern 0 (_ = _) => refine eq_refl : typeclass_instances.
  Goal exists (f : Foo nat), @foo _ f = 0.
  Proof.
    unshelve (notypeclasses refine (ex_intro _ _ _)). 
    Set Typeclasses Debug. Set Printing All.
    all:once (typeclasses eauto).
    Fail idtac. (* Check no subgoals are left *)
    Undo 3.
    (** In this case, the (_ = _) subgoal is not considered 
        by typeclass resolution *)
    refine (ex_intro _ _ _). Fail reflexivity.
  Abort.

End RefineVsNoTceauto.

Module Leivantex2PR339.
  (** Was a bug preventing to find Local hints associated with no pattern *)
  Class Bar := {}.
  Instance bar1 (t:Type) : Bar := {}.
  Local Hint Extern 0 => exact True : typeclass_instances.
  Typeclasses eauto := debug.
  Goal Bar.
    Set Typeclasses Debug Verbosity 2.
    typeclasses eauto. (* Relies on resolution of a non-class subgoal *)
    Undo 1.
    typeclasses eauto with typeclass_instances.
  Qed.
End Leivantex2PR339.

Module HintMode_NonStuck_Failure_Refine_DoNotShelve.

Class test (x : nat) := testv : True.
Local Hint Mode test ! : typeclass_instances.
Record foo := { n : nat ; t : test n ; h : t = t }.
Goal True.
  (* This tests that non-stuck classes whose resolution fails
     are left as proper subgoals and not shelved if failure is allowed.
  *)
  simple refine (let name := (_ : test 5) in _); [|].
Abort.
End HintMode_NonStuck_Failure_Refine_DoNotShelve.

Module bt.
Require Import Equivalence.

Record Equ (A : Type) (R : A -> A -> Prop).
Definition equiv {A} R (e : Equ A R) := R.
Record Refl (A : Type) (R : A -> A -> Prop).
Axiom equ_refl : forall A R (e : Equ A R), Refl _ (@equiv A R e).
Local Hint Extern 0 (Refl _ _) => unshelve class_apply @equ_refl; [shelve|] : foo.

Variable R : nat -> nat -> Prop.
Lemma bas : Equ nat R.
Admitted.
Local Hint Resolve bas : foo.
Local Hint Extern 1 => match goal with |- (_ -> _ -> Prop) => shelve end : foo.

Goal exists R, @Refl nat R.
  eexists.
  Set Typeclasses Debug.
  (* Fail solve [unshelve eauto with foo]. *)
  Set Typeclasses Debug Verbosity 1.
  Test Typeclasses Depth.
  solve [typeclasses eauto with foo].
Qed.

Set Typeclasses Compatibility "8.5".
Parameter f : nat -> Prop.
Parameter g : nat -> nat -> Prop.
Parameter h : nat -> nat -> nat -> Prop.
Axiom a : forall x y, g x y -> f x -> f y.
Axiom b : forall x (y : Empty_set), g (fst (x,y)) x.
Axiom c : forall x y z, h x y z -> f x -> f y.
Local Hint Resolve a b c : mybase.
Goal forall x y z, h x y z -> f x -> f y.
  intros.
  (* Fail Timeout 1 typeclasses eauto with mybase. Loops now *)
  Unshelve.
Abort.
End bt.
Generalizable All Variables.

Module mon.

Reserved Notation "'return' t" (at level 0).
Reserved Notation "x >>= y" (at level 65, left associativity).



Record Monad {m : Type -> Type} := {
  unit : forall {α}, α -> m α where "'return' t" := (unit t) ;
  bind : forall {α β}, m α -> (α -> m β) -> m β where "x >>= y" := (bind x y) ;
  bind_unit_left : forall {α β} (a : α) (f : α -> m β), return a >>= f = f a }.

Print Visibility.
Print unit.
Arguments unit {m _ α}.
Arguments Monad : clear implicits.
Notation "'return' t" := (unit t).

(* Test correct handling of existentials and defined fields. *)

Class A `(e: T) := { a := True }.
Class B `(e_: T) := { e := e_; sg_ass :> A e }.

(* Set Typeclasses Debug. *)
(* Set Typeclasses Debug Verbosity 2. *)

Goal forall `{B T}, Prop.
  intros. apply a.
Defined.

Goal forall `{B T}, Prop.
  intros. refine (@a _ _ _).
Defined.

Class B' `(e_: T) := { e' := e_; sg_ass' :> A e_ }.

Goal forall `{B' T}, a.
  intros. exact I.
Defined.

End mon.

(* Correct treatment of dependent goals *) 

(* First some preliminaries: *)

Section sec.
  Context {N: Type}.
  Class C (f: N->N) := {}.
  Class E := { e: N -> N }.
  Context
    (g: N -> N) `(E) `(C e)
    `(forall (f: N -> N), C f -> C (fun x => f x))
    (U: forall f: N -> N, C f -> False).

(* Now consider the following: *)

  Let foo := U (fun x => e x).
  Check foo _.

(* This type checks fine, so far so good. But now
 let's try to get rid of the intermediate constant foo.
 Surely we can just expand it inline, right? Wrong!: *)
 Check U (fun x => e x) _.
End sec.

Module UniqueSolutions.
  Set Typeclasses Unique Solutions.
  Class Eq (A : Type) : Set.
    Instance eqa : Eq nat := {}.
    Instance eqb : Eq nat := {}.

    Goal Eq nat.
      try apply _.
      Fail exactly_once typeclasses eauto.
    Abort.
End UniqueSolutions.


Module UniqueInstances.
  (** Optimize proof search on this class by never backtracking on (closed) goals
      for it. *)
  Set Typeclasses Unique Instances.
  Class Eq (A : Type) : Set.
    Instance eqa : Eq nat. Qed.
    Instance eqb : Eq nat := {}.
    Class Foo (A : Type) (e : Eq A) : Set.
    Instance fooa : Foo _ eqa := {}.

    Tactic Notation "refineu" open_constr(c) := unshelve refine c.

    Set Typeclasses Debug.
    Goal { e : Eq nat & Foo nat e }.
      unshelve refineu (existT _ _ _).
      all:simpl.
      (** Does not backtrack on the (wrong) solution eqb *)
      Fail all:typeclasses eauto.
    Abort.
End UniqueInstances.

Module IterativeDeepening.

  Class A.
  Class B.
  Class C.

  Instance: B -> A | 0 := {}.
  Instance: C -> A | 0 := {}.
  Instance: C -> B -> A | 0 := {}.
  Instance: A -> A | 0 := {}.
  
  Goal C -> A.
    intros.
    (* Fail Timeout 1 typeclasses eauto. *)
    Set Typeclasses Iterative Deepening.
    Fail typeclasses eauto 1.
    typeclasses eauto 2.
    Undo.
    Unset Typeclasses Iterative Deepening.
    (* Fail Timeout 1 typeclasses eauto. *)
    Set Typeclasses Iterative Deepening.
    typeclasses eauto.
  Qed.

End IterativeDeepening.

Module AxiomsAreNotInstances.

  Class TestClass2 := {}.
  Axiom testax2 : TestClass2.
  Fail Definition testdef2 : TestClass2 := _.

  (* we didn't break typeclasses *)
  Existing Instance testax2.
  Definition testdef2 : TestClass2 := _.

End AxiomsAreNotInstances.

Module HintIf.

(* Prolog program *)
(* b(1). *)
(* b(2). *)
(* c(2,1). *)
(* e(1). *)
(* d(3,3). *)
(* a(X,Y) :- b(X), c(X,Y), !, e(X). % fail *)
(* a(X,Y) :- d(X,Y).  % cut away *)
(* ?- a(A,B). % should fail *)

(* Coq translation *)

Class a (x y : nat).
Class b (x : nat).
Class c (x y : nat).
Class d (x y : nat).
Class e (x : nat).

Definition b1 : b 1 := Build_b _.
Local Hint Extern 0 (b _) => exact b1 : typeclass_instances.
Definition b2 : b 2 := Build_b _.
Local Hint Extern 1 (b _) => exact b2 : typeclass_instances.
Definition b3 : b 3 := Build_b _.
Local Hint Extern 2 (b _) => exact b3 : typeclass_instances.
Definition c21 : c 2 1 := Build_c _ _.
Local Hint Extern 0 (c _ _) => exact c21 : typeclass_instances.
Definition e1 : e 1 := Build_e _.
Local Hint Extern 0 (e _) => exact e1 : typeclass_instances.
Definition bcea x y `{b x} `{c x y} `{e x} : a x y := Build_a _ _.
Local Hint Extern self 0 (a ?x ?y)
  when notypeclasses refine (@bcea _ _ _ _ _);
    once (only 1-2: self) => self
  : typeclass_instances.

(* once ensures we do not backtrack and try b3. *)

Definition da x y `{d x y} : a x y :=  Build_a _ _.
Local Hint Extern 1 (a _ _) => refine (@da _ _ _) : typeclass_instances.
Definition d33 : d 3 3 := Build_d _ _.
Local Hint Extern 0 (d _ _) => exact d33 : typeclass_instances.

Set Typeclasses Debug Verbosity 2.
Goal exists x, exists y, a x y.
Proof.
eexists; eexists.
Fail typeclasses eauto.
Show Proof.
Abort.
End HintIf.
