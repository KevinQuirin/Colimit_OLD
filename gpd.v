Require Import HoTT HoTT.hit.Truncations Connectedness Utf8_core.
Require Import colimit.


Set Universe Polymorphism.
Global Set Primitive Projections. 
Set Implicit Arguments.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

Section Gpd.

  Definition Gpd_graph : graph.
  Proof.
    refine (Build_graph _ _).
    exact nat.
    intros n m. exact (S n = m).
  Defined.

  Definition Gpd_aux {X Y:Type} (f: X -> Y) (n:nat) : {T:Type & T -> Y}.
  Proof.
    induction n.
    - exists X. exact f.
    - exists (Coeq (@pullback_pr1 Y IHn.1 IHn.1 IHn.2 IHn.2) (@pullback_pr2 Y IHn.1 IHn.1 IHn.2 IHn.2)).
      refine (Coeq_rec _ _ _).
      exact IHn.2. intro b. apply pullback_commsq.
  Defined.
  
  Definition Gpd {X Y:Type} (f: X -> Y) : diagram Gpd_graph.
  Proof.
    refine (Build_diagram _ _ _).
    - intros i. exact (Gpd_aux f i).1.
    - intros i j q; destruct q; simpl.
      exact coeq.
  Defined.

End Gpd.

Section Colimit_truncation.

  Require Import VD_truncation.
  Variable X:Type.
  Let D := @Gpd X Unit (λ x, tt).
  Let Q := colimit D.
  Let D' := @Gpd_ X.

  Lemma PB_unit_is_prod (A B: Type)
    : Pullback (λ x:A, tt) (λ x:B, tt) <~> A*B.
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - intros [a [b p]]; exact (a,b).
    - intros [a b]; exact (a;(b;path_ishprop _ _)).
    - intros [a b]; reflexivity.
    - intros [a [b p]]; apply path_sigma' with 1; apply path_sigma' with 1.
      apply path_ishprop.
  Defined.

  Lemma Gpd_aux_is_tt : forall i, (Gpd_aux (λ _ : X, tt) i).2 = λ x, tt.
  Proof.
    intro i. apply path_forall; intro x.
    apply path_ishprop.
  Defined.
  
  Lemma Gpd_aux_is_Gpd_aux_ : forall i, (Gpd_aux (λ _ : X, tt) i).1 = Gpd_aux_ X i.
  Proof.
    induction i.
    reflexivity.
    simpl.
    apply path_universe_uncurried.
    refine (equiv_functor_coeq' _ _ _ _).
    refine (equiv_adjointify _ _ _ _).
    intro x; cbn in *.
    apply (transport (λ U:Type, U*U) IHi).
    exact (pullback_pr1 x, pullback_pr2 x).
    
    intro x.
    exists (transport (λ U, U) IHi^ (fst x)).
    exists (transport (λ U, U) IHi^ (snd x)).
    apply path_ishprop.
    
    abstract (
        intro x;
        rewrite transport_prod; cbn; repeat rewrite transport_pV; reflexivity
      ).
    
    abstract (
        intro x; refine (path_sigma' _ _ _);
        [rewrite transport_prod; simpl; rewrite transport_Vp; reflexivity |
         rewrite transport_sigma; simpl;
         refine (path_sigma' _ _ _);
         [rewrite transport_const; rewrite transport_prod; simpl;
          rewrite transport_Vp; reflexivity |
          apply path_ishprop] ]
      ).

    apply equiv_path; exact IHi.
    abstract (intro x; simpl; rewrite transport_prod; reflexivity ).
    abstract (intro x; simpl; rewrite transport_prod; reflexivity ).
  Defined.

    
  Theorem Gpd_is_Gpd_ : Q <~> (Trunc (-1) X).
  Proof.
    assert (H : D = D').
    {
      apply path_diagram.
      refine (exist _ _ _).
      
      apply path_forall; intro i. apply Gpd_aux_is_Gpd_aux_.
      intros i j x. destruct x. simpl.
      intro x.
      unfold ap10, path_forall. repeat rewrite eisretr.
      apply (moveL_transport_V idmap).
      simpl.
      rewrite transport_path_universe_uncurried.
      reflexivity. }
    unfold Q.
    
    etransitivity; try exact (VD_truncation X). unfold D' in H; destruct H.
    exact equiv_idmap.
  Defined.
    
End Colimit_truncation.

Section Colimit_Gpd.

  Definition Gpd_cocone (X Y:Type) (f:X -> Y)
  : cocone (Gpd f) Y.
  Proof.
    refine (exist _ _ _).
    - intro i. simpl. exact (Gpd_aux f i).2.
    - intros i j f0 x. destruct f0. reflexivity.
  Defined.
  
  Axiom VD_Giraud : forall (X Y:Type), forall (f:X -> Y), IsSurjection f -> (is_colimit (Gpd_cocone f)).
                                                                               
End Colimit_Gpd.