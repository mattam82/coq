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
Implicit Arguments unit [[m] [m0] [α]].
Implicit Arguments Monad [].
Notation "'return' t" := (unit t).

(* Test correct handling of existentials and defined fields. *)

Class A `(e: T) := { a := True }.
Class B `(e_: T) := { e := e_; sg_ass :> A e }.

Goal forall `{B T}, a.
  intros. exact I.
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

Module IterativeDeepening.

  Class A.
  Class B.
  Class C.

  Instance: B -> A | 0.
  Instance: C -> A | 0.
  Instance: C -> B -> A | 0.
  Instance: A -> A | 0.
  
  Goal C -> A.
    intros.
    Set Typeclasses Debug.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    typeclasses eauto.
  Qed.

End IterativeDeepening.

Module Cut.
  Class A.
  Class B.
  Instance ba : B -> A | 0.
  Instance ab : A -> B | 0.
             
  Hint Cut [!*; ab; !*; ba] : typeclass_instances.
  Hint Cut [!*; ba; !*; ab] : typeclass_instances.
  Set Typeclasses Debug.
  Check (_ : A).
  Check (_ : B).
End Cut.  
