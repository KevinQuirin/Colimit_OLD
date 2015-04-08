Require Import Utf8_core.
Require Import HoTT.
Require Import equivalence cech_nerve colimit colimit2.

Set Implicit Arguments.
Context `{fs : Funext}.
Context `{ua : Univalence}.

(* Squash *)
Notation sq A := (@tr -1 A).  

(* We want to prove that [Trunc -1 A] is the colimit of the Cech nerve of [sq: A -> Trunc -1 A]. *)

Section Prod_diagram.
  
  (* We prove here that we can use the real diagram A×...×A -> ... -> A×A -> A instead of the Cech nerve of sq with irrelevant second compenents *)

  Lemma ishprop_pullback_sq_pr2
        (A : Type)
        (i : nat)
        (x : ∃ P : A ∧ hProduct A i, char_hPullback (sq A) i P)
  : IsHProp
      (char_hPullback (sq A) i x.1).
    induction i; simpl.
    apply true_ishprop.
    refine (trunc_prod). simpl in *.
    exact (IHi (snd x.1; snd x.2)).
  Qed.

  Definition prod_diag (A:Type) : diagram Cech_nerve_graph.
    refine (Build_diagram _ _ _).
    - simpl. intro i. exact (hProduct A (S i)).
    - simpl. intros i j [f q]. destruct f. intros x.
      exact (forget_hProduct A (S j) x q).
  Defined.

  Definition CN_sq_cocone (A:Type) Q (C : cocone (prod_diag A) Q)
  : cocone (Cech_nerve_diagram (sq A)) Q.
    destruct C as [q qq].
    refine (exist _ _ _); simpl.
    - intros i X. apply (q i). exact X.1.
    - intros i j [f [k Hk]] x; destruct f; simpl.
      exact (qq (j.+1) j (idpath,(k;Hk)) x.1).
  Defined.
  
  Lemma inhab_pullback_sq_pr2 (A:Type) (i:nat)
  : forall x:A*(hProduct A i), char_hPullback (sq A) i x.
    intro x.
    induction i. exact tt. simpl.
    refine (pair _ _).
    apply path_ishprop.
    apply IHi.
  Qed.

  Lemma colim_prod_diag_CN_sq (A:Type) Q (C : cocone (prod_diag A) Q)
  : is_colimit (prod_diag A) Q C -> is_colimit (Cech_nerve_diagram (sq A)) Q (CN_sq_cocone C).
    intros H.
    refine (transport_is_colimit _ _ _ _ _ _ _ _ _ _ _ _ H); simpl.
    - intro i. refine (equiv_adjointify _ _ _ _).
      + intros x. exists x. apply inhab_pullback_sq_pr2.
      + exact pr1.
      + intros x. apply path_sigma' with idpath.
        simpl. refine (path_ishprop _ _). apply ishprop_pullback_sq_pr2.
      + intros x. reflexivity.
    - intros i j [f [q Hq]]; destruct f; simpl.
      intro x; reflexivity.
    - reflexivity.
    - simpl.
      apply path_forall; intro i.
      apply path_forall; intro j.
      apply path_forall; intros [f [q Hq]]; destruct f.
      apply path_forall; intro x. simpl. hott_simpl.
      unfold path_sigma'.
      pose (p := @pr1_path_sigma). unfold pr1_path in p. rewrite p.
      hott_simpl.
  Qed.

End Prod_diagram.



Section TheProof.

  Open Scope path_scope.
  Open Scope type_scope.

  (* Sketch of proof :
     Let [Q] be the colimit of [prod_diag A].
     As [Trunc -1 A] defines a cocone on [prod_diag A], we have an arrow [Q -> Trunc -1 A].
     As there is an arrow [A -> Q], it remains to show that [IsHProp Q], so that we have an arrow [Trunc -1 A -> Q] defining an equivalence ([Q] and [Trunc -1 A]) are both [HProp]). *)

  (* To show [IsHProp Q], it suffices to show that : *)
  Lemma HProp_if_snd_equiv (Q:Type)
  : IsEquiv (snd : Q*Q -> Q) -> IsHProp Q.
  Proof.
    intro H.
    apply hprop_allpath; intros u v.
    assert (X : (u,u) = (v,u)).
    { apply (@equiv_inj _ _ _ H). reflexivity. }
    exact (ap fst X).
  Qed.

  Lemma popo A B C : (A <~> B) -> (A * C <~> B * C).
    intros F.
    refine (equiv_adjointify _ _ _ _).
    intros x. exact (F (fst x), snd x).
    intros x. exact (F^-1 (fst x), snd x).
    intros x. simpl. by rewrite eisretr.
    intros x. simpl. by rewrite eissect.
  Defined.

  
  Variable (A:Type).
  Let D := prod_diag A.
  (* Let D' := Cech_nerve_diagram (sq A). *)
  Variable Q : Type.
  Variable C : cocone D Q.
  Variable (colimQ : is_colimit D Q C).

  Let pi := @snd Q A.
  
  Ltac funext a := apply path_forall; intros a.


  Lemma C2
  : cocone (pdt_diagram_l D Q) Q.
    refine (exist _ _ _).
    - simpl. intros i [a [x y]]. exact ((C.1 i) (pi (a,x), y)).
    - intros i j f x; destruct (fst f); simpl in *.
      exact (C.2 (j.+1) j f _).
  Defined.
  
  Lemma isequiv_snd_QQ_if_isequiv_snd_QA
  : IsEquiv (pi : Q*A -> A) -> IsEquiv (snd : Q*Q -> Q).
    intro H.
    specialize (colimit_product_l Q colimQ); intros colimQQ.
    set (C1 := pdt_cocone_l Q C) in *. set (D' := pdt_diagram_l D Q) in *.
    unfold is_colimit in colimQQ.
    assert (eq: @snd Q Q  = (map_to_cocone C1 Q)^-1 C2).
    { apply (equiv_inj (map_to_cocone C1 Q)).
      rewrite eisretr. refine (path_sigma _ _ _ _ _).
      + funext i. apply path_forall; intros [a [x y]]. simpl. reflexivity.
      + admit.
      }
    rewrite eq; clear eq.
    apply (colimit_unicity colimQQ).
    refine (transport_is_colimit _ _ _ _ _ _ _ _ _ _ _ _ colimQ).
    - intros i. simpl. symmetry.
      transitivity ((Q ∧ A) ∧ hProduct A i).
      apply equiv_prod_assoc. apply popo. refine (BuildEquiv _ _ _ H).
    - intros i j f x. admit.
    - reflexivity. 
    - simpl. admit.
  Defined.

  
End TheProof.
