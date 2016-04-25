(* Library added by Théo Zimmermann 2016 *)

Require Export Coq.Program.Basics Coq.Classes.CMorphisms.
Require Coq.Setoids.Setoid.

Global Set Universe Polymorphism.

Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) : Type :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
                           (right associativity, at level 55) : type_scope.

Local Notation " A <-> B " := (iffT A B) : type_scope.

Section Definitions.

  Set Implicit Arguments.
  Variables A B : Type.
  Variable R : A -> B -> Type.

  (** * Totality declarations *)

  (** Surjectivity, i.e. right-totality *)
  Definition righttotal := ((R ##> arrow) ##> arrow) forall_def forall_def.

  (** Left-totality *)
  Definition lefttotal := ((R ##> flip arrow) ##> flip arrow) forall_def forall_def.

  (** Both right and left-totality *)
  Definition bitotal := ((R ##> iffT) ##> iffT) forall_def forall_def.

  (** * Uniqueness declarations *)

  (** Functionality, i.e. right-uniqueness *)
  Definition rightunique := (R ##> R ##> arrow) eq eq.

  (** Injectivity, i.e. left-uniqueness *)
  Definition leftunique := (R ##> R ##> flip arrow) eq eq.

  (** Both right and left-unique *)
  Definition biunique := (R ##> R ##> iffT) eq eq.

  (** Definition of "bounded forall" *)
  Definition ball (subType : A -> Type) (predicate : A -> Type) :=
    forall x, subType x -> predicate x.

End Definitions.

(** ** Ltac to solve automatically some goals which just need reordering of hypotheses *)

Ltac apply_hyp :=
  match goal with
    [ H : _ |- _ ] => apply H
  end.

Ltac intro_and_apply :=
  apply_hyp + (intros ? * ; intro_and_apply).

Ltac flipdecl := 
  lazy beta delta;
  repeat (
      repeat split;
      repeat intro_and_apply
    ).

Section Declarations1.

  Variables A B : Type.
  Variable R : A -> B -> Type.
  
  (** * Totality declarations *)

  (** ** Straightforward properties *)
  
  Lemma fliptotal : righttotal (flip R) <-> lefttotal R.
  Proof. flipdecl. Qed.

  Lemma flipbitotal : bitotal (flip R) <-> bitotal R.
  Proof. flipdecl. Qed.
  
  Lemma bitotal_from_right_and_left_total : righttotal R -> lefttotal R -> bitotal R.
  Proof. flipdecl. Qed.

  (** ** More complex properties *)
  
  Theorem righttotal_decl : (forall x' : B, { x : A & R x x'}) <-> righttotal R.
  Proof.
    lazy delta zeta.
    split; intros Hsurj.
    - intros p p' Hp Hall x'.
      destruct (Hsurj x') as [x Rx].
      now apply (Hp x _).
    - apply (Hsurj (fun _ => True) _); trivial.
      intros x x' Rx _.
      now exists x.
  Qed.

  Lemma bitotal_decl_recip1 : bitotal R -> (forall x' : B, { x : A & R x x' }).
  Proof.
    intro bitotal.
    apply (bitotal (fun _ => True) (fun x' => { x : A & R x x'})); firstorder.
  Qed.

  Lemma righttotal_from_bitotal : bitotal R -> righttotal R.
  Proof.
    intro bitotal.
    apply righttotal_decl.
    apply bitotal_decl_recip1.
    assumption.
  Qed.

  (** * Uniqueness declarations *)

  (** ** Straightforward properties *)
  
  Lemma flipunique : rightunique (flip R) <-> leftunique R.
  Proof. flipdecl. Qed.

  Lemma flipbiunique : biunique (flip R) <-> biunique R.
  Proof. flipdecl. Qed.

  Lemma biunique_from_right_and_left_unique : rightunique R -> leftunique R -> biunique R.
  Proof. flipdecl. Qed.

  Lemma rightunique_from_biunique : biunique R -> rightunique R.
  Proof. flipdecl. Qed.

  Lemma leftunique_from_biunique : biunique R -> leftunique R.
  Proof. flipdecl. Qed.

  (** ** More complex properties *)

  Theorem rightunique_decl :
    (forall x x' y', R x x' -> R x y' -> x' = y') <-> rightunique R.
  Proof.
    split.
    - intros functional x x' relx y y' rely eq.
      apply (functional x); trivial.
      now rewrite eq.
    - intros rightunique x **.
      generalize (eq_refl x).
      now apply rightunique.
  Qed.

  Theorem biunique_decl_recip1 : biunique R -> forall x x' y', R x x' -> R x y' -> x' = y'.
  Proof.
    intro biunique.
    apply rightunique_decl.
    apply rightunique_from_biunique.
    assumption.
  Qed.

  Lemma generic_right_covered_decl :
    ((R ##> arrow) ##> arrow) forall_def (fun P' => forall y, { x : A & R x y } -> P' y).
  Proof.
    lazy beta delta.
    intros P P' Prel HP x' (x & xrel).
    apply (Prel _ _ xrel).
    apply HP.
  Qed.

End Declarations1.

Section Declarations2.

  Variables A B C D : Type.
  Variable R : A -> B -> Type.
  Variable S : C -> D -> Type.
  
  (** * Totality declarations *)

  (** ** Properties derived from their right-equivalent *)

  Theorem lefttotal_decl : (forall x : A, { x' : B & R x x'}) <-> lefttotal R.
  Proof.
    eapply iffT_Transitive; [ | exact (fliptotal _) ].
    eapply iffT_Transitive; [ | exact (righttotal_decl _) ].
    reflexivity.
  Qed.
  
  Lemma bitotal_decl_recip2 : bitotal R -> (forall x : A, { x' : B & R x x' }).
  Proof.
    intro bitotal.
    apply bitotal_decl_recip1.
    apply flipbitotal.
    assumption.
  Qed.

  Lemma lefttotal_from_bitotal : bitotal R -> lefttotal R.
  Proof.
    intro bitotal.
    apply fliptotal.
    apply righttotal_from_bitotal.
    apply flipbitotal.
    assumption.
  Qed.

  Lemma generic_left_covered_decl :
    ((R ##> flip arrow) ##> flip arrow) (fun P => forall x, { y : B & R x y } -> P x) forall_def.
  Proof.
    pose (H := @generic_right_covered_decl B A (flip R)).
    lazy beta delta.
    intros P P' Prel HP x' (x & xrel).
    apply (Prel _ _ xrel).
    apply HP.
  Qed.

  (** ** Properties derived from their right and left-equivalent *)

  Theorem bitotal_decl :
    (forall x' : B, { x : A & R x x'}) ->
    (forall x : A, { x' : B & R x x'}) ->
    bitotal R.
  Proof.
    intros righttotal lefttotal.
    apply righttotal_decl in righttotal.
    apply lefttotal_decl in lefttotal.
    now apply bitotal_from_right_and_left_total.
  Qed.

  (** *** Generic property for non-total relations *)
  
  Theorem generic_covered_decl :
    let coveredA := fun x => { y : B & R x y } in
    let coveredB := fun y => { x : A & R x y } in
    ((R ##> iffT) ##> iffT) (ball coveredA) (ball coveredB).
  Proof.
    lazy beta delta zeta.
    intros P P' relP.
    split.
    - apply generic_right_covered_decl.
      firstorder.
    - apply generic_left_covered_decl.
      firstorder.
  Qed.
    
  (** ** More complex properties *)

  Theorem righttotal_predicate : rightunique R <-> righttotal (R ##> iffT).
  Proof.
    split.
    - intros rightunique.
      apply righttotal_decl.
      intros P'.
      exists (fun x => forall x', R x x' -> P' x').
      (*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
      split; unfold arrow; firstorder.
      erewrite rightunique; eauto.
    - intros righttotal x x' relx y y' rely ->.
      assert ({ P : A -> Type & (R ##> iffT) P (eq x') }) as (P & HP)
          by now apply righttotal_decl.
      apply HP in relx.
      apply HP in rely.
      apply rely.
      apply relx.
      reflexivity.
  Qed.

  (** * Uniqueness declarations *)

  (** ** Properties derived from their right-equivalent *)

  Theorem leftunique_decl :
    (forall x y y', R x y' -> R y y' -> x = y) <-> leftunique R.
  Proof.
    eapply iffT_Transitive; [ | exact (flipunique _) ].
    eapply iffT_Transitive; [ | exact (rightunique_decl _) ].
    flipdecl.
  Qed.

  Theorem biunique_decl_recip2 : biunique R -> forall x y y', R x y' -> R y y' -> x = y.
  Proof.
    intros biunique *.
    apply flipbiunique in biunique.
    now apply (biunique_decl_recip1 biunique).
  Qed.

  (** ** Properties derived from their right and left-equivalent *)
  
  Theorem biunique_decl :
    (forall x x' y', R x x' -> R x y' -> x' = y') ->
    (forall x y y', R x y' -> R y y' -> x = y) ->
    biunique R.
  Proof.
    intros.
    apply biunique_from_right_and_left_unique.
    - now apply rightunique_decl.
    - now apply leftunique_decl.
  Qed.
    
  (** ** More complex properties *)  

  Lemma rightunique_predicate :
    righttotal R ->
    ((R ##> iffT) ##> (R ##> iffT) ##> arrow) (eq ##> iffT) (eq ##> iffT).
  Proof.
    intros righttotal P P' relP Q Q' relQ H x' * <-.
    assert ({ x : A & R x x' }) as (x & Hx)
        by now apply righttotal_decl.
    pose proof Hx as Hx2.
    specialize (H x x eq_refl).
    apply relP in Hx.
    apply relQ in Hx2.
    firstorder.
  Qed.

End Declarations2.

Section Declarations3.

  Variables A B C D : Type.
  Variable R : A -> B -> Type.
  Variable S : C -> D -> Type.
  
  (** * Totality declarations *)

  (** ** Properties derived from their right-equivalent *)
  
  Theorem lefttotal_predicate : leftunique R <-> lefttotal (R ##> iffT).
  Proof.
    eapply iffT_Transitive; [ | exact (fliptotal _) ].
    eapply iffT_Transitive; [ symmetry; exact (flipunique _) | ].
    eapply iffT_Transitive; [ exact (righttotal_predicate _) | ].
    flipdecl.
  Qed.

  (** ** Properties derived from their right and left-equivalent *)

  Theorem total_predicate : biunique R <-> bitotal (R ##> iffT).
  Proof.
    split.
    - intro biunique.
      apply bitotal_from_right_and_left_total;
        [ apply righttotal_predicate;
          apply rightunique_from_biunique
        | apply lefttotal_predicate;
          apply leftunique_from_biunique ];
        exact biunique.
    - intro bitotal.
      apply biunique_from_right_and_left_unique;
        [ apply righttotal_predicate;
          apply righttotal_from_bitotal
        | apply lefttotal_predicate;
          apply lefttotal_from_bitotal ];
        exact bitotal.
  Qed.

  (* ** A lemma that is not a generalization of the previous one unfortunately. *)
  
  Lemma bitotal_function :
    biunique R -> bitotal R -> bitotal S -> bitotal (R ##> S).
  Proof.
    intros biunique_R bitotal_R bitotal_S.
    apply bitotal_decl.
    - pose (rightunique_R := biunique_decl_recip1 biunique_R).
      pose (lefttotal_R := bitotal_decl_recip2 bitotal_R).
      pose (righttotal_S := bitotal_decl_recip1 bitotal_S).
      intros f'.
      exists (fun x : A => projT1 (righttotal_S (f' (projT1 (lefttotal_R x))))).
      intros x x' relx.
      specialize (rightunique_R x x' (projT1 (lefttotal_R x)) relx).
      rewrite <- rightunique_R.
      + destruct (righttotal_S (f' x')); auto.
      + destruct (lefttotal_R x); auto.
    - pose (leftunique_R := biunique_decl_recip2 biunique_R).
      pose (righttotal_R := bitotal_decl_recip1 bitotal_R).
      pose (lefttotal_S := bitotal_decl_recip2 bitotal_S).
      intro f.
      exists (fun x' : B => projT1 (lefttotal_S (f (projT1 (righttotal_R x'))))).
      intros x x' relx.
      specialize (leftunique_R x (projT1 (righttotal_R x')) x' relx).
      rewrite <- leftunique_R.
      + destruct (lefttotal_S (f x)); auto.
      + destruct (righttotal_R x'); auto.
  Qed.

  (** * Uniqueness declarations *)

  (** ** Properties derived from their right-equivalent *)
  
  Lemma leftunique_predicate :
    lefttotal R ->
    ((R ##> iffT) ##> (R ##> iffT) ##> flip arrow) (eq ##> iffT) (eq ##> iffT).
  Proof.
    intros lefttotal.
    apply fliptotal in lefttotal.
    apply rightunique_predicate in lefttotal.
    intros P P' ? Q Q' ?.
    specialize (lefttotal P' P ltac:(flipdecl) Q' Q ltac:(flipdecl)).
    assumption.
  Qed.

  (** ** Properties derived from their right and left-equivalent *)

  Lemma biunique_predicate :
    bitotal R ->
    ((R ##> iffT) ##> (R ##> iffT) ##> iffT) (eq ##> iffT) (eq ##> iffT).
  Proof.
    intro bitotal.
    pose (righttotal := righttotal_from_bitotal bitotal).
    pose (lefttotal := lefttotal_from_bitotal bitotal).
    intros P P' relP Q Q' relQ; split;
      [ apply (rightunique_predicate righttotal relP relQ)
      | apply (leftunique_predicate lefttotal relP relQ) ];
      assumption.
  Qed.

End Declarations3.
