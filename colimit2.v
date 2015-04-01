Require Import Utf8_core.
Require Import HoTT.
Require Import colimit.


Section cocone_product.
  
  Context `{fs : Funext}.

  Variable G:graph.
  Variable D: diagram G.

  Variable A: Type.
  
  Definition pdt_diagram : diagram G.
    refine (Build_diagram _ _ _).
    + intros i. exact ((D i) * A).
    + simpl. intros i j f x. exact (diagram1 D f (fst x), snd x).
  Defined.

 
  Definition pdt_cocone {Q: Type} (C: cocone D Q) : cocone pdt_diagram (Q * A).
    unfold cocone in *.
    refine (exist _ _ _). simpl in *.
    intros i z. exact (C.1 i (fst z) , snd z).
    intros i j f z. simpl.
    f_ap. exact (C.2 _ _ _ _).
  Defined.


  Lemma cocone_product : forall (X:Type), cocone pdt_diagram X <~> cocone D (A -> X).
    intros X.
    refine (equiv_adjointify _ _ _ _).
    + intros C. unfold cocone in *.
      refine (exist _ _ _).
      intros i x a. exact (C.1 i (x, a)).
      intros i j f x. simpl. apply path_forall; intros a.
      exact (C.2 _ _ _ (x,a)).
    + intros C. unfold cocone in *.
      refine (exist _ _ _).
      intros i z. exact (C.1 i (fst z) (snd z)).
      intros i j f z. simpl.
      f_ap. exact (C.2 _ _ _ _).
    + intros [q pp]. simpl.
      refine (path_sigma _ _ _ _ _).
      - reflexivity.
      - simpl. repeat (apply path_forall; intro). apply eta_path_forall.
    + intros [q pp]. simpl.
      refine (path_sigma _ _ _ _ _).
      - reflexivity.
      - simpl. repeat (apply path_forall; intro). unfold path_forall.
        rewrite eisretr. reflexivity.
  Defined.

    
  Lemma colimit_product (Q:Type) (C: cocone D Q) (H: is_colimit D Q C) : is_colimit pdt_diagram (Q * A) (pdt_cocone C).
    unfold is_colimit. intros X.
    assert (H': map_to_cocone (pdt_cocone C) X = ((cocone_product X)^-1) o (map_to_cocone C (A -> X)) o ((equiv_uncurry Q _ X)^-1)).
    + apply path_forall; intros F.
      refine (path_sigma _ _ _ _ _).
      - reflexivity.
      - simpl.
        apply path_forall; intros i.
        apply path_forall; intros j.
        apply path_forall; intros f.
        apply path_forall; intros z.
        destruct (C.2 i j f (fst z)). simpl.
        reflexivity.
    + rewrite H'. refine isequiv_compose.
      refine isequiv_compose. apply H.
  Defined.

End cocone_product.



Section colimit_unicity.

  Definition postcompose {A X Y: Type} (f: X->Y) : (A->X) -> (A->Y) :=
    fun g => f o g.
    

  Lemma yoneda_map (A B: Type) (F: forall X, Equiv (A->X) (B->X))
        (H: forall (X Y: Type) (i: X->Y), (postcompose i) o (F X) == (F Y) o (postcompose i))
  : IsEquiv ((F B)^-1 idmap).
    set (f := (F B)^-1 idmap). set (g := (F A) idmap).
    refine (isequiv_adjointify _ g _ _).
    + specialize (H _ _ f idmap). unfold postcompose in H.
      apply ap10. rewrite H.
      apply eisretr.
    + specialize (H _ _ g f). apply ap10.
      apply (equiv_inj (F A)). unfold postcompose in H.
      rewrite <- H. unfold f. rewrite (eisretr (F B)). reflexivity.
  Defined.

   

  Context `{fs : Funext}.
 
  Lemma map_to_cocone_postcompose (G: graph) (D: diagram G) (P: Type) (C: cocone D P) (X Y: Type) (f: X->Y)
  : (map_to_cocone C Y) o (postcompose f) == (λ C, map_to_cocone C _ f) o (map_to_cocone C X).
    intros g. destruct C as [q pq].
    refine (path_cocone _ _  _ _ _ _ _).
    + intros i x. reflexivity.
    + unfold postcompose. simpl.
    intros i j f0 x.  hott_simpl. apply ap_compose.
  Defined.


  Lemma colimit_unicity (G: graph) (D: diagram G) (P Q: Type) (C: cocone D P) (C': cocone D Q) (colimP : is_colimit D P C) (colimQ : is_colimit D Q C')
  : P <~> Q.
    unfold is_colimit in *.
    set (φP := map_to_cocone C) in *.
    set (φQ := map_to_cocone C') in *.
    refine (BuildEquiv _ _ _  (yoneda_map _ _ _ _)).
    + intros X. transitivity (cocone D X).
      refine (BuildEquiv _ _ (φP X) _).
      refine (BuildEquiv _ _ (φQ X)^-1 _). 
    + intros X Y i q. simpl. 
      transitivity ((φQ Y)^-1 (map_to_cocone (φP X q) _ i)).
      - assert (H: forall C, postcompose i ((φQ X)^-1 C) =   (φQ Y)^-1 (map_to_cocone C _ i)); [|apply H].
        clear colimP φP C. intros C.
        apply (equiv_inj (φQ Y)). rewrite eisretr.
        specialize (map_to_cocone_postcompose _ D _ C' _ _ i ((φQ X)^-1 C)); intros H.
        rewrite eisretr in H. assumption.
      - apply ap. symmetry. apply map_to_cocone_postcompose.
  Defined.
        
End colimit_unicity.
