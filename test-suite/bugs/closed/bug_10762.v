Set Implicit Arguments.
Generalizable Variables A B.
Parameter val : Type.

(* Set Typeclasses Strict Resolution.
 *)
Class Enc (A:Type) : Type :=
  make_Enc { enc : A -> val }.

Hint Mode Enc + : typeclass_instances.

Instance Enc_val : Enc val.
Proof using. constructor. eapply (fun (x:val) => x). Defined.

Class Decode (v:val) `{EA:Enc A} (V:A) : Type :=
  make_Decode { decode : v = enc V }.

Arguments decode v {A} {EA} {V} {Decode}.

Instance Decode_enc : forall `{EA:Enc A} (V:A),
  Decode (enc V) V.
Proof using. intros. constructor. auto. Defined.
Unset Typeclass Resolution After Apply.
Parameter val_one : val -> val.

Definition One A `{EA:Enc A} (V:A) : val :=
  val_one (enc V).

Instance Decode_one : forall `{EA:Enc A} (V:A) (v:val),
  Decode v V ->
  Decode (val_one v) (One V).
Proof using.
  intros. unfold One. eapply make_Decode.
  simpl. f_equal. inversion H. auto.
Qed.


Parameter P : val -> Prop.

Parameter foo : forall (v:val) A1 (EA1:Enc A1) (X:A1),
 (Decode v X) -> P v.
 Set Typeclasses Debug Verbosity  2.
 Set Printing All.

Lemma test_in_strict_resolution_mode : forall B `{EB:Enc B} (Y:B),
 P (val_one (enc Y)).
Proof.
  (* The intention of this proof is to apply [foo]
     and instantiate [X] with [One Y]. *)
  intros.
  eapply @foo.
  (* notypeclasses refine (@foo _ _ _ _ _). *)
  Show Existentials.
  (* here [?X] has type [?A1] with [?EA1:Enc ?A1] unresolved. *)
  (* Now, typeclass resolution fails. *)
  simple eapply @Decode_one.
  Show Existentials.

  (* Observe how a manual application of Decode_one introduces
     fresh [?A] and [?EA:Enc ?A], and refines [?X] to [One ?V],
     and [?A1] to [val]. *)
  Show Existentials.
  eauto with typeclass_instances.
  (* Question: why is [eauto with typeclass_instances]
     not attempting to apply Decode_one? *)
Abort.

(* Play this proof after commenting strict resolution and the
   lemma above. *)
Lemma test_without_strict_resolution_mode : forall B `{EB:Enc B} (Y:B),
 P (val_one (enc Y)).
Proof.
  intros.
  (* Remark: here, if not using "Set Typeclasses Strict Resolution.",
     then [eapply @foo] would systematically instantiate [A1]
     as [A], even though there is not absolutely evidence that
     this the right thing to do. In that case,
     [notypeclasses refine (@foo _ _ _ _ _)] is necessary. *)
  (* eapply @foo. Show Existentials. *)
(*   eapply foo.
 *)  notypeclasses refine (@foo _ _ _ _ _).
  Show Existentials.
  (* here, typeclass resolution succeeds, by applying Decode_one. *)
  (* eapply Decode_one. Show Existentials. *)
  eauto with typeclass_instances.
Abort.
