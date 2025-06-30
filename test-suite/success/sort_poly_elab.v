Set Universe Polymorphism.
Set Sort Polymorphism.
Set Printing Universes.


Module Reduction.

  Definition qsort := 𝒰.
  (* qsort@{α | u |} = 𝒰@{α | u} : 𝒰@{u+1} *)

  Definition qsort' : 𝒰 := 𝒰.
  (* qsort'@{α | u u0 |} = 𝒰@{α | u0} : 𝒰@{u} *)

  Monomorphic Universe U.

  Definition tU := 𝒰@{U}.
  Definition qU := qsort@{Type ; U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso (A:𝒰) (H:False) : A := match H with end.
  (* exfalso@{α | u |} : forall A : 𝒰@{α | _}, False -> A *)

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type|Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type|Set}.

  Fixpoint iter (A:𝒰) (f:A -> A) n x :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.
  (* iter@{α | u |} : forall (A : 𝒰@{α | u}) (_ : forall _ : A, A) (_ : nat) (_ : A), A *)

  Definition iterType := Eval lazy in iter@{Type;_}.

  Definition iterSProp := Eval lazy in iter@{SProp;_}.

End Reduction.

Module Conversion.

  Inductive Box (A:𝒰) := box (_:A).
  (* Box@{α α0 | u |} (A : 𝒰@{α | u}) : 𝒰@{α0 | u} *)


  Definition t1 (A:𝒰) (x y : A) := box _ x.
  (* t1@{α α0 | u |} : forall (A : 𝒰@{α | u}) (_ : A) (_ : A), Box@{α α0 | u} A *)
  Definition t2 (A:𝒰) (x y : A) := box _ y.
  (* t2@{α α0 | u |} : forall (A : 𝒰@{α | u}) (_ : A) (_ : A), Box@{α α0 | u} A *)

  Definition t1' (A:𝒰) (x y : A) := x.
  (* t1'@{α | u |} : forall (A : 𝒰@{α | u}) (_ : A) (_ : A), A *)
  Definition t2' (A:𝒰) (x y : A) := y.

  Fail Check eq_refl : t1 nat = t2 nat.
  Fail Check eq_refl : t1' nat = t2' nat.

  Check fun A:SProp => eq_refl : t1 A = t2 A.
  (* : forall A : SProp,
       @eq (forall (_ : A) (_ : A), Box@{SProp Type | sort_poly_elab.475} A)
         (t1@{SProp Type | sort_poly_elab.475} A)
         (t2@{SProp Type | sort_poly_elab.475} A) *)

  Check fun A:SProp => eq_refl : box _ (t1' A) = box _ (t2' A).
  (* : forall A : SProp,
       @eq
         (Box@{SProp Type | sort_poly_elab.479} (forall (_ : A) (_ : A), A))
         (box@{SProp Type | sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t1'@{SProp | sort_poly_elab.480} A))
         (box@{SProp Type | sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t2'@{SProp | sort_poly_elab.482} A)) *)

  Definition ignore {A:𝒰} (x:A) := tt.
  (* ignore@{α | u |} : forall {A : 𝒰@{α | u}} (_ : A), unit *)

  Definition unfold_ignore (A:𝒰) : ignore (t1 A) = ignore (t2 A) := eq_refl.
  (* unfold_ignore@{α α0 α1 | u |} : forall A : 𝒰@{α | u},
       @eq unit
         (@ignore@{α0 | u} (forall (_ : A) (_ : A), Box@{α α0 | u} A)
            (t1@{α α0 | u} A))
         (@ignore@{α1 | u} (forall (_ : A) (_ : A), Box@{α α1 | u} A)
            (t2@{α α1 | u} A)) *)

  Definition t (A:SProp) := Eval lazy in t1 A.
  (* t@{α ; u |} : forall (A : SProp) (_ : A) (_ : A), Box@{SProp α ; u} A *)

  Axiom v : forall (A:𝒰), bool -> A.
  Fail Check fun P (x:P (v@{Type;_} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).
    (* : forall (A : SProp) (P : A -> Type@{sort_poly_elab.105}),
       P (v@{SProp | sort_poly_elab.104} A true) ->
       P (v@{SProp | sort_poly_elab.106} A false) *)
End Conversion.

Module Inference.
  Definition zog (A:𝒰) := A.
  (* zog@{α | u |} : 𝒰@{α | _} -> 𝒰@{α | _} *)

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag (A:𝒰) := zog A.
  (* zag@{α | u |} : 𝒰@{α | _} -> 𝒰@{α | _} *)

  (* implicit type of A gets unified to 𝒰@{s|u} *)
  Definition zig A := zog A.
  (* zig@{α | u |} : 𝒰@{α | _} -> 𝒰@{α | _} *)

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s'; |} (A:𝒰@{s;Set}) := zog@{s';} A.
End Inference.

Module Inductives.
  Inductive foo1 : 𝒰 := .
  (* foo1@{α | u |} : 𝒰@{α | _} :=  . *)

  Fail Check foo1_sind.

  (* Fails if constraints cannot be extended *)
  Fail Definition foo1_False@{s;+|} (x : foo1@{s;_}) : False := match x return False with end.
  (* Elimination constraints are not implied by the ones declared: s ~> Prop *)

  Definition foo1_False@{s;+|+} (x : foo1@{s;_}) : False := match x return False with end.
  (* s | u |= s ~> Prop *)

  Definition foo1_False' (x : foo1) : False := match x return False with end.
  (* foo1_False'@{α | u |} : foo1@{α | u} -> False *)
  (* α | u |= α ~> Prop *)

  Inductive foo2 := Foo2 : 𝒰 -> foo2.
  (* foo2@{α | u |} : Type@{α | u+1} *)
  Check foo2_rect.

  Inductive foo3 (A : 𝒰) := Foo3 : A -> foo3 A.
  (* foo3@{α α0 ; u |} (A : Type@{α | u}) : Type@{α0 | u} *)
  Check foo3_rect.

  Inductive foo5 (A : 𝒰) : Prop := Foo5 (_ : A).
  (* foo5@{α | u |} (A : 𝒰@{α | u}) : Prop := *)

  Definition foo5_ind' : forall (A : 𝒰) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.

  Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> 𝒰)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.

  Definition foo5_Prop_rect' (A : Prop) (P : foo5 A -> 𝒰)
    (H : forall a, P (Foo5 A a))
    (f : foo5@{Prop|_} A)
    : P f
    := match f with Foo5 _ a => H a end.

  (* all sort poly output with nonzero contructors are squashed (avoid interfering with uip) *)
  Inductive foo6 : 𝒰 := Foo6.
  Fail Check foo6_sind.

  Definition foo6_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6)
    : P f
    := match f with Foo6 => H end.

  Definition foo6_prop_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6@{Prop|_})
    : P f
    := match f with Foo6 => H end.

  Definition foo6_type_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6@{Type|_})
    : P f
    := match f with Foo6 => H end.

  Inductive foo7 : 𝒰 := Foo7_1 | Foo7_2.
  Fail Check foo7_sind.
  Fail Check foo7_ind.

  Definition foo7_prop_ind (P:foo7 -> Prop)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop|})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Definition foo7_prop_rect (P:foo7 -> 𝒰)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Set Primitive Projections.
  Set Warnings "+records".

  Fail Record R1 : 𝒰 := {}.
  (* The record R1 could not be defined as a primitive record because it has no projections. *)
  
  Record R2 (A:SProp) : 𝒰 := { R2f1 : A }.

  Goal forall (A:SProp) (r2 : R2@{Type;0} A), r2 = {| R2f1 := r2.(R2f1 A) |}.
  Proof. intros A r2. Fail reflexivity. Abort.
  (* The command has indeed failed with message:
      In environment
      A : SProp
      r2 : R2 A
      Unable to unify "{| R2f1 := R2f1 _ r2 |}" with "r2". *)

  Fail Goal forall (A:SProp) (r2 : R2@{SProp;0} A), r2 = {| R2f1 := r2.(R2f1 A) |}. (* FIXME *)
  (* Proof. intros A r2. reflexivity. Abort. *)

  (* R3@{SProp Type|} may not be primitive  *)
  Record R3 (A:𝒰) : 𝒰 := { R3f1 : A }.

  Fail Example R3_same_sort@{s;u} (A :𝒰@{s;u}) : forall (r3 : R3@{s s;u} A), r3 = {| R3f1 := r3.(R3f1 A) |}. (* FIXME *)
  (* Proof. intros r3. reflexivity. Qed. *)

  Goal forall (A:SProp) (r3 : R3@{_ Type;0} A), r3 = {| R3f1 := r3.(R3f1 A) |}.
  Proof. intros A r3. Fail reflexivity. Abort.

  Fail Goal forall (A:SProp) (r3 : R3@{_ SProp;u} A), r3 = {| R3f1 := r3.(R3f1 A) |}. (* FIXME *)
  (* Proof. intros A r3. reflexivity. Abort. *)

  Record R4@{s; |} (A:𝒰@{s;Set}) : 𝒰@{s;Set} := { R4f1 : A}.

  (* non SProp instantiation must be squashed *)
  Fail Record R5@{s;u} (A:𝒰@{s;u}) : SProp := { R5f1 : A}.
  (* The command has indeed failed with message:
     The record R5 could not be defined as a primitive record because it is squashed. *)
  Fail #[warnings="-non-primitive-record"]
    Record R5 (A:𝒰) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Fail #[warnings="-non-primitive-record,-cannot-define-projection"]
    Record R5 (A:𝒰) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Record R6@{s;u} (A:𝒰@{s;0}) : 𝒰@{s;0} := { R6f1 : A; R6f2 : nat }.
  (* s ; u |= s -> Type *)
  
  Fail Check fun (A:SProp) (x y : R6@{SProp;_} A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  (* The command has indeed failed with message:
      The quality constraints are inconsistent: cannot enforce SProp -> Type because it would identify Type and SProp which is inconsistent.
      This is introduced by the constraints SProp -> Type *)
  Fail Check fun (A:Prop) (x y : R6@{Prop;_} A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  (* The command has indeed failed with message:
      The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
      This is introduced by the constraints Prop -> Type *)

  Fail Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).
(* The term "A" has type "SProp" while it is expected to have type "𝒰@{α148 ; Set}" (universe inconsistency: Cannot enforce SProp <= Type@{α148 | Set}). *)

  (* Elimination constraints are accumulated by fields, even on independent fields *)
  #[projections(primitive=no)] Record R7 (A:𝒰) := { R7f1 : A; R7f2 : nat }.
  (* Record R7@{α α0 | u |} (A : 𝒰@{α | u}) : 𝒰@{α0 | max(Set,u)}  *)
  (* R7f1@{α α0 | u |} : forall A : 𝒰@{α | u}, R7@{α α0 | u} A -> A
      α α0 | u |= α0 ~> α *)
  (* R7f2@{α α0 | u |} : forall A : 𝒰@{α | u}, R7@{α α0 | u} A -> nat
      α α0 | u |= α0 ~> α
                  α0 ~> Type *)

  Unset Primitive Projections.

  (* Elimination constraints are accumulated by fields *)
  Record R8 := {
    R8f1 : 𝒰;
    R8f2 : R8f1
  }.
  (* Record R8@{α α0 | u |} : 𝒰@{α | u+1}. *)
  (* R8f1@{α α0 | u |} : R8@{α α0 | u} -> 𝒰@{α0 | u}
      α α0 | u |= α ~> Type *)
  (* R8f2@{α α0 | u |} : forall r : R8@{α α0 | u}, R8f1@{α α0 | u} r
      α α0 | u |= α ~> α0
                  α ~> Type *)

  Inductive sigma (A:𝒰) (B:A -> 𝒰) : 𝒰
    := pair : forall x : A, B x -> sigma A B.
  (* Inductive sigma@{α α0 α1 | u u0 |} (A : 𝒰@{α | u}) (B : A -> 𝒰@{α0 | u0}) : 𝒰@{α1 | max(u,u0)} *)

  Definition sigma_srect A B
    (P : sigma A B -> 𝒰)
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.

  (* Elimination constraints are added *)
  Definition pr1 {A B} (s:sigma A B) : A
    := match s with pair _ _ x _ => x end.
  (* α α0 α1 | u u0 |= α1 ~> α *)

  Definition pr2 {A B} (s:sigma A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.
  (* α α0 α1 | u u0 |= α1 ~> α
                       α1 ~> α0 *)

  Inductive seq (A:𝒰) (a:A) : A -> Prop := seq_refl : seq A a a.
  (* Inductive seq@{α | u |} (A : 𝒰@{α | u}) (a : A) : A -> Prop *)
  Arguments seq_refl {_ _}.

  Definition eta A B (s:sigma A B) : seq _ s (pair A B (pr1 s) (pr2 s)).
  Proof.
    destruct s. simpl. reflexivity.
  Qed.

  Set Primitive Projections.
  Set Warnings "+records".
  (* sigma as a primitive record works better *)
  Record Rsigma (A:𝒰) (B:A -> 𝒰) : 𝒰
    := Rpair { Rpr1 : A; Rpr2 : B Rpr1 }.

  (* match desugared to primitive projections using definitional eta *)
  Fail Definition Rsigma_srect A B
    (P : Rsigma A B -> 𝒰)
    (H : forall x b, P (Rpair _ _ x b))
    (s:Rsigma A B)
    : P s
    := match s with Rpair _ _ x b => H x b end.

  (* sort polymorphic exists (we could also make B sort poly)
     can't be a primitive record since the first projection isn't defined at all sorts *)
  Inductive sexists (A:𝒰) (B:A -> Prop) : Prop
    := sexist : forall a:A, B a -> sexists A B.

  (* we can eliminate to Prop *)
  Check sexists_ind.


  Definition π1 {A:𝒰} {P:A -> 𝒰} (p : sigma@{_ _ Type;_ _ _} A P) : A :=
    match p return A with pair _ _ a _ => a end.

End Inductives.


Set Universe Polymorphism.

Inductive sigma (A:𝒰) (P:A -> 𝒰) : 𝒰
  :=  exist : forall x:A, P x -> sigma A P.

Inductive sum@{sl sr s;ul ur} (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) : 𝒰@{s;max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
Fail Definition sum_elim@{sl sr s0 s0';ul ur v|}
  (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> 𝒰@{s0';v})
  (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
  match x with
  | inl a => fl a
  | inr b => fr b
  end.
(* The command has indeed failed with message:
Elimination constraints are not implied by the ones declared: s0->s0' *)

(* Using + to elaborate missing constraints. Definition passes *)
Definition sum_elim@{sl sr s0 s0';ul ur v|+}
  (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> 𝒰@{s0';v})
  (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
  match x with
  | inl a => fl a
  | inr b => fr b
  end.
(* sl sr s0 s0' ; ul ur v |= s0 -> s0' *)

Definition sum_sind := sum_elim@{Type Type Type SProp;_ _ _}.
Definition sum_rect := sum_elim@{Type Type Type Type;_ _ _}.
Definition sum_ind := sum_elim@{Type Type Type Prop;_ _ _}.

Definition or_ind := sum_elim@{Prop Prop Prop Prop;_ _ _}.
Definition or_sind := sum_elim@{Prop Prop Prop SProp;_ _ _}.
Fail Definition or_rect := sum_elim@{Prop Prop Prop Type;_ _ _}.
(* The command has indeed failed with message:
The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identifyType and Prop which is inconsistent.
This is introduced by the constraints Type -> Prop *)

Definition sumor := sum@{Type Prop Type;_ _}.

Definition sumor_sind := sum_elim@{Type Prop Type SProp;_ _ _}.
Definition sumor_rect := sum_elim@{Type Prop Type Type;_ _ _}.
Definition sumor_ind := sum_elim@{Type Prop Type Prop;_ _ _}.

(* Implicit constraints are elaborated *)
Definition idT@{sl sr s;ul ur} (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Type;ul ur} A B :=
  match x return sum@{sl sr Type;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s -> Type *)

(* Implicit constraints are elaborated *)
Definition idP@{sl sr s;ul ur} (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Prop;ul ur} A B :=
  match x return sum@{sl sr Prop;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s -> Prop *)

(* Implicit constraints are elaborated *)
Definition idS@{sl sr s;ul ur} (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr SProp;ul ur} A B :=
  match x return sum@{sl sr SProp;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s -> SProp *)

(* Implicit constraints are elaborated *)
Definition idV@{sl sr s s';ul ur} (A : 𝒰@{sl;ul}) (B : 𝒰@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr s';ul ur} A B :=
  match x return sum@{sl sr s';ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s s' ; ul ur |= s->s' *)

Fail Compute idV@{Prop Type Prop Type;Set Set} (inl I).

Inductive List'@{s s';l} (A : 𝒰@{s;l}) : 𝒰@{s';l} :=
| nil' : List' A
| cons' : A -> List' A -> List' A.

Arguments nil' {A}.
Arguments cons' {A} _ _.

Definition list'_elim@{s s0 s';l l'}
  (A : 𝒰@{s;l}) (P : List'@{s s0;l} A -> 𝒰@{s';l'})
  (fn : P nil') (fc : forall (x : A) (l : List' A), P l -> P (cons' x l)) :=
  fix F (l : List'@{s s0;l} A) : P l :=
    match l with
    | nil' => fn
    | cons' x l => fc x l (F l)
    end.
(* s s0 s' ; l l' |= s0->s' *)

Fixpoint list'_idT@{s s';l} {A : 𝒰@{s;l}} (l : List'@{s s';l} A) : List'@{s Type;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idT l)
  end.
(* s s' ; l |= s'->Type *)

Fixpoint list'_idP@{s s';l} {A : 𝒰@{s;l}} (l : List'@{s s';l} A) : List'@{s Prop;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idP l)
  end.
(* s s' ; l |= s'->Prop *)

Fixpoint list'_idS@{s s';l} {A : 𝒰@{s;l}} (l : List'@{s s';l} A) : List'@{s SProp;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idS l)
  end.
(* s s' ; l |= s'->SProp *)

(* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
Fail Fixpoint list'_idV@{s s0 s';l l'|l <= l'} {A : 𝒰@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.
(* The command has indeed failed with message:
Elimination constraints are not implied by the ones declared: s0->s' *)

(* Using + to elaborate missing constraints. Definition passes *)
Fixpoint list'_idV@{s s0 s';l l'|l <= l' + } {A : 𝒰@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.
(* s s0 s' ; l l' |= s0->s', l <= l' *)

Inductive False'@{s;u} : 𝒰@{s;u} :=.

Definition False'_False@{s; +|+} (x : False'@{s;_}) : False := match x return False with end.
(* s ; u |= s->Prop *)

Inductive bool@{s;u} : 𝒰@{s;u} := true | false.

Definition bool_to_Prop@{s;u} (b : bool@{s;u}) : Prop.
Proof.
  destruct b.
  - exact True.
  - exact False.
Defined.
(* s ; u |= s->Type *)

Definition bool_to_True_conj@{s;u} (b : bool@{s;u}) : True \/ True.
Proof.
  destruct b.
  - exact (or_introl I).
  - exact (or_intror I).
Defined.
(* s ; u |= s->Prop *)

Program Definition bool_to_Prop'@{s;u} (b : bool@{s;u}) : Prop := _.
Next Obligation.
  intro b; destruct b.
  - exact True.
  - exact False.
Defined.
(* s ; u |= s->Type *)

Inductive unit@{s;u} : 𝒰@{s;u} := tt.

#[universes(polymorphic=no)]
Sort Test.
(* Sort variables not instantiated *)
Fail Check (match true@{Test;Set} return ?[P] with true => tt | false => tt end).

(* Interactive definition *)
Inductive FooNat : 𝒰 :=
| FO : FooNat
| FS : FooNat -> FooNat.

Definition Foo (n : FooNat) : FooNat.
  destruct n.
  - exact FO.
  - exact FO.
Defined.

Check Foo@{Type Prop;}.
Fail Check Foo@{Prop Type;}.
