Set Universe Polymorphism.

(** listings: true eq false **)
Lemma true_false_sprop: true@{SProp|} = false@{SProp|}.
Proof. reflexivity. Qed.
(** listings: end **)

(** listings: bool param **)
Inductive bool_par@{s_0 s_1 s_par| |} : bool@{s_0|} -> bool@{s_1|} -> Type@{s_par|Set} :=
  | true_par : bool_par true true
  | false_par : bool_par false false.

Definition negb_par@{s_0 s_1 s_par| |} (b_0:bool@{s_0|}) (b_1:bool@{s_1|}) (b_par:bool_par b_0 b_1)
  : bool_par (negb b_0) (negb b_1) :=
  match b_par in bool_par a b return bool_par (negb a) (negb b) with
    | true_par => false_par
    | false_par => true_par
  end.
(** listings: end **)

(** listings: LargeElimSort **)
Class LargeElimSort@{s|l|} :=
{ Univ : Type@{s|l+1} ;  code : Type@{s|l} -> Univ ;   El : Univ -> Type@{s|l} ;
  El_code A : El (code A) = A :> Type@{s|l} ; code_El a : code (El a) = a :> Univ }.
(** listings: end **)

Fail Definition P@{s| |}(b : bool@{s|}) :=
  match b return Type@{s|Set} with
    true => unit@{s|}
  | false => empty@{s|}
  end.

Definition P@{s|u|} {H:LargeElimSort@{s|u}} (b : bool@{s|}) :=
  match b return H.(Univ) with
    true => code unit
  | false => code empty
  end.

Lemma eq_true@{s|u|} {H:LargeElimSort@{s|u}} : forall (b:bool@{s|}), true = b -> H.(El) (P b).
Proof.
  intros b e.  destruct e. cbn. rewrite H.(El_code). exact tt.
Qed.

(** listings: neq true false **)
Lemma neq_true_false@{s|u|} {H:LargeElimSort@{s|u}} : true@{s|} = false -> empty@{s|}.
(** listings: end **)

Proof.
  intro e. rewrite <- (H.(El_code) _). exact (eq_true _ e).
Qed.
