Require Import MyTacs HoTT.
Require Import equivalence lemmas colimit.

Context `{fs : Funext}.


Section Coproduct.

  Definition coproduct_graph : graph.
    refine (Build_graph _ _).
    - exact Bool.
    - intros A B; exact Empty.
  Defined.

  Definition coproduct_diag (A B: Type) : diagram coproduct_graph.
    refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact A. exact B.
    - intros i j; destruct i, j; intro H; destruct H.
  Defined.
  
  Definition coproduct_cocone (A B: Type)
  : cocone (coproduct_diag A B) (A + B).
    refine (exist _ _ _).
    - intros i x; destruct i. exact (inl x). exact (inr x).
    - intros i j f x; destruct i, j, f.
  Defined.

  Lemma is_coproduct_coproduct (A B: Type)
  : is_colimit (coproduct_cocone A B).
    intros X.
    refine (isequiv_adjointify _ _ _ _).
    - intros C x. destruct x. exact (C.1 true a). exact (C.1 false b).
    - intros C. refine (path_cocone _ _).
      + intros i x; destruct i; reflexivity.
      + intros i j f x; destruct i, j, f.
    - intros F. funext x; destruct x; reflexivity.
  Defined.

End Coproduct.



Section Coequalizer.

  Definition coequalizer_graph : graph.
    refine (Build_graph _ _).
    - exact Bool.
    - intros i j; exact (if i then if j then Empty else Bool else Empty).
  Defined.

  Definition coequalizer_diag {B A: Type} (f g: B -> A) : diagram coequalizer_graph.
    refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact B. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact f. exact g.
  Defined.
  
  Definition coequalizer_cocone {B A: Type} (f g: B -> A)
  : cocone (coequalizer_diag f g) (Coeq f g).
    refine (exist _ _ _).
    - intros i x; destruct i; simpl in *. exact (coeq (g x)). exact (coeq x).
    - intros i j φ x; destruct i, j, φ; simpl. exact (cp x). reflexivity.
  Defined.

  Lemma is_coequalizer_coequalizer {B A: Type} (f g: B -> A)
  : is_colimit (coequalizer_cocone f g).
    intros X.
    refine (isequiv_adjointify _ _ _ _).
    - intros C. refine (Coeq_rec _ _ _). exact (C.1 false).
      intros b. etransitivity.
      exact (C.2 true false true b).
      exact (C.2 true false false b)^.
    - intros C. refine (path_cocone _ _).
      + intros i x; destruct i; simpl. exact (C.2 true false false x). reflexivity.
      + intros i j φ x; destruct i, j, φ; simpl.
        * hott_simpl.
          match goal with
            | [|- ap (Coeq_rec ?a ?b ?c) _ @ _ = _ ] => rewrite (Coeq_rec_beta_cp a b c)
          end. hott_simpl.
        * reflexivity.
    - intros F. apply path_forall.
      match goal with
        | [|- ?G == _ ] => refine (Coeq_ind (λ w, G w = F w) _ _)
      end.
      + simpl. reflexivity.
      + intros b. simpl.
        rewrite transport_paths_FlFr.
        rewrite Coeq_rec_beta_cp. hott_simpl.
  Defined.

End Coequalizer.



Section Pushout.

  Inductive Pushout_graph_shape :=
    |Pushout_Corner : Pushout_graph_shape
    |Pushout_Right : Pushout_graph_shape
    |Pushout_Down : Pushout_graph_shape.
  
  Definition pushout_graph : graph.
    refine (Build_graph _ _).
    - exact Pushout_graph_shape.
    - intros A B. induction A.
      induction B.
      exact Empty.
      exact Unit.
      exact Unit.
      exact Empty.
      exact Empty.
  Defined.

  Definition pushout_diag {A B C:Type} (f:A -> B) (g:A -> C) : diagram pushout_graph.
    refine (Build_diagram _ _ _).
    - intro x; induction x.
      exact A. exact B. exact C.
    - intros i j; induction i, j; try (intro H; destruct H); simpl.
      exact f. exact g.
  Defined.

  Definition pushout_cocone_build {A B C:Type} (f:A -> B) (g:A -> C) {P: Type} (pi1: B -> P) (pi2: C -> P)
             (H: pi1 o f == pi2 o g)
  : cocone (pushout_diag f g) P.
    refine (exist _ _ _).
    - induction i; simpl. exact (pi1 o f). exact pi1. exact pi2.
    - induction i; induction j; induction f0; simpl. reflexivity. intros a. exact (H a)^.
  Defined.

  Definition pushout_cocone {A B C:Type} (f:A -> B) (g:A -> C)
  : cocone (pushout_diag f g) (pushout f g).
    refine (pushout_cocone_build f g _ _ _).
    exact (push o inl). exact (push o inr). exact Pushout.pp.
  Defined.

  Lemma is_pushout_pushout {A B C:Type} (f:A -> B) (g:A -> C)
  : is_colimit (pushout_cocone f g).
    intros X. refine (isequiv_adjointify _ _ _ _).
    - intros Co. refine (pushout_rec _ _ _).
      + intros x; induction x. exact (Co.1 Pushout_Right a). exact (Co.1 Pushout_Down b).
      + intros a. simpl. etransitivity. exact (Co.2 Pushout_Corner Pushout_Right tt a).
        exact (Co.2 Pushout_Corner Pushout_Down tt a)^.
    - intros Co.
      refine (path_cocone _ _).
      + induction i; intros x; simpl; try reflexivity. exact (Co.2 Pushout_Corner Pushout_Right tt x).
      + induction i, j, f0; simpl. reflexivity.
        intros x. hott_simpl. rewrite <- inverse_ap.
        match goal with
          | [|-  (ap (pushout_rec ?a ?b ?c) _)^ @ _ = _ ] => rewrite (pushout_rec_beta_pp a b c x)
        end. rewrite inv_pp. hott_simpl.
    - intros F. funext x. simpl.
      match goal with
        | [|- pushout_rec _ ?pu ?pp _ = _ ] => set (push' := pu); set (pp' := λ a : A, ap F (Pushout.pp a)); transitivity (pushout_rec _ push' pp' x)
      end.
      apply ap10. apply ap. subst pp'.
      funext a. hott_simpl.
      refine (pushout_ind f g (λ x, pushout_rec X push' pp' x = F x) _ _ x).
      + induction a; reflexivity.
      + intros a; simpl.
        rewrite transport_paths_FlFr.
        rewrite pushout_rec_beta_pp. hott_simpl.
  Defined.
  
End Pushout.