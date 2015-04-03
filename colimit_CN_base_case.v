Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.
Require Import equivalence lemmas colimit cech_nerve nat_lemmas colimit2.

(* We want to prove that [Trunc -1 A] is the colimit of the Cech nerve of [tr: A -> Trunc -1 A]. *)

Section Prod_diagram.
  
  (* We prove here that we can use the real diagram A×...×A -> ... -> A×A -> A instead of the Cech nerve of tr with irrelevant second compenents *)

  Context `{ua : Univalence}.
  Context `{fs : Funext}.

  Lemma ishprop_pullback_tr_pr2
        (A : Type)
        (i : nat)
        (x : ∃ P : A ∧ hProduct A i, char_hPullback (λ a : A, tr (n:=-1) a) i P)
  : IsHProp
      (char_hPullback (λ a : A, tr (n:=-1) a) i (let (proj1_sig, _) := x in proj1_sig)).
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

  Definition CN_tr_cocone (A:Type)
  : cocone (Cech_nerve_diagram (λ a:A, tr (n:=-1) a)) (colimit (prod_diag A)).
    refine (exist _ _ _); simpl.
    - intros i X.
      apply (@colim (Cech_nerve_graph) _ i). exact X.1.
    - intros i j [f [q Hq]] x; destruct f; simpl.
      exact (pp (Cech_nerve_graph) (prod_diag A) (j.+1) j (idpath,(q;Hq)) x.1).
  Defined.

  Lemma inhab_pullback_tr_pr2 (A:Type) (i:nat)
  : forall x:A*(hProduct A i), char_hPullback (λ a : A, tr (n:=-1) a) i x.
    intro x.
    induction i. exact tt. simpl.
    refine (pair _ _).
    apply path_ishprop.
    apply IHi.
  Qed.

  Lemma colim_prod_diag_CN_tr (A:Type)
  : is_colimit (Cech_nerve_diagram (λ a:A, tr (n:=-1) a)) (colimit (prod_diag A)) (CN_tr_cocone A).
    refine (transport_is_colimit (Cech_nerve_graph) (prod_diag A) _ _ _ _ _ _ _ _ _ _ (colimit_is_colimit _ (prod_diag A))); simpl.
    - intro i. refine (equiv_adjointify _ _ _ _).
      + intros x. exists x. apply inhab_pullback_tr_pr2.
      + exact pr1.
      + intros x. apply path_sigma' with idpath.
        simpl. refine (path_ishprop _ _). apply ishprop_pullback_tr_pr2.
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

  Context `{fs : Funext}.
  Context `{ua : Univalence}.
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

  Variable (A:Type).
  Let D := prod_diag A.
  Let Q := colimit D.
  Let colimQ := colimit_is_colimit _ D.
          
  Lemma isequiv_snd_QQ_if_isequiv_snd_QA
  : IsEquiv (snd : Q*A -> A) -> IsEquiv (snd : Q*Q -> Q).
    intro H.
    pose (foo := colimit_product_r _ _ A _ _ colimQ). fold Q in foo.
    
  Admitted.


  
End TheProof.
