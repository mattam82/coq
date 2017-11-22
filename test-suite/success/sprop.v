
Definition iUnit : SProp := forall A : SProp, A -> A.

Definition itt : iUnit := fun A a => a.

Definition iUnit_irr (P : iUnit -> Type) (x y : iUnit) : P x -> P y
  := fun v => v.

Definition iSquash (A:Type) : SProp := forall P : SProp, (A -> P) -> P.
Definition isquash A : A -> iSquash A := fun a P f => f a.
Definition iSquash_rect A (P : iSquash A -> SProp) (H : forall x, P (isquash A x))
  : forall x : iSquash A, P x := fun x => x (P x) H.

Inductive sBox (A:SProp) : Prop := sbox : A -> sBox A.

Definition uBox := sBox iUnit.

Definition sBox_irr A (x y : sBox A) : x = y.
Proof.
  destruct x as [x], y as [y].
  reflexivity.
Defined.

Set Primitive Projections.
(* Primitive record with all fields in SProp has the eta property of SProp so must be SProp. *)
Record rBox (A:SProp) : Prop := rmkbox { relem : A }.

(* Check that it doesn't have eta *)
Fail Check (fun (A : SProp) (x : rBox A) => eq_refl : x = @rmkbox _ (@relem _ x)).

Inductive sEmpty : SProp := .

Inductive sUnit : SProp := stt.

Inductive BIG : SProp := foo | bar.

Inductive Squash (A:Type) : SProp
  := squash : A -> Squash A.

Definition BIG_flip : BIG -> BIG.
Proof.
  intros [|]. exact bar. exact foo.
Defined.

Inductive pb : Prop := pt | pf.

Definition pb_big : pb -> BIG.
Proof.
  intros [|]. exact foo. exact bar.
Defined.

Fail Definition big_pb (b:BIG) : pb :=
  match b return pb with foo => pt | bar => pf end.

Inductive sNZ : nat -> SProp := snz : forall n, sNZ (S n).

Definition sPred (n:nat) (s:sNZ n) : nat :=
  match s with snz k => k end.

Definition spred1 n (s : sNZ (S n)) : sPred _ s = sPred _ (snz n) := eq_refl.
Definition spred2 n (s : sNZ (S n)) : sPred _ (snz n) = n := eq_refl.
Definition spred3 n (s:sNZ _) : sPred _ s = n := eq_trans (spred1 n s) (spred2 n s).

Inductive Ispair (A:Type) (B:A -> Type) : sigT B -> SProp :=
  ispair : forall x y, Ispair A B (existT B x y).

Definition p1 A B p (i : Ispair A B p) : A :=
  match i with ispair _ _ x _ => x end.

(* TODO
Definition spred3' n (s:sNZ _) : sPred n s = n := eq_refl.


Inductive sprod (A B : SProp) : SProp := spair : A -> B -> sprod A B.

and the reduction stuff *)
