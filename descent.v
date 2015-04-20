Require Export Utf8_core.
Require Import HoTT.
Require Import equivalence lemmas colimit.
Require Import MyTacs.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.

Section Dependent_diagrams.

  Context `{fs : Funext}.

  (** We define here the graph ∫D, also denoted G·D *)
  Definition integral (G:graph) (D:diagram G) : graph.
    refine (Build_graph _ _).
    - exact {i:G & D i}.
    - intros i j. exact {g:G i.1 j.1 & diagram1 D g i.2 = j.2}.
  Defined.

  (** Then, a dependent diagram E over D is just a diagram over ∫D. *)
  Definition dep_diagram' {G:graph} (D:diagram G) := diagram (integral G D).

  (** It is actually easier to use the following *)
  Definition dep_diagram {G:graph} (D:diagram G) := {E0 : forall (i:G), D i -> Type & forall (i j:G) (g:G i j) (u:D i), E0 i u -> E0 j (diagram1 D g u)}.

  (** They are indeed equivalent *)
  Lemma dep_diagram_simpl {G:graph} (D:diagram G)
  : dep_diagram' D <~> dep_diagram D.
    unfold dep_diagram.
    refine (equiv_adjointify _ _ _ _).
    - intros U.
      refine (exist _ _ _).
      intros i u. exact (U (i;u)).
      simpl. intros i j f u.
      refine (diagram1 U _).
      simpl. exists f. reflexivity.
    - intros X.
      refine (Build_diagram _ _ _); simpl.
      intros u. exact (X.1 u.1 u.2).
      intros [i u] [j v] [f p]; simpl in *. destruct p. refine (X.2 _ _ _ _).
    - intros X; simpl. reflexivity.
    - intros X; simpl.
      destruct X as [q qq].
      apply path_diagram.
      refine (exist _ _ _); simpl.
      reflexivity.
      intros [u r] [v s] [w p]; simpl in *. destruct p.
      intro x; reflexivity.
  Qed.

  Definition sum_diagram {G:graph} {D:diagram G} (E : dep_diagram D) : diagram G.
    refine (Build_diagram _ _ _).
    - intro i. exact {u:D i & E.1 i u}.
    - intros i j f x. simpl in *.
      exists (diagram1 D f x.1).
      exact (E.2 i j f x.1 x.2).
  Defined.

  Lemma foo (A:Type) (χ : A -> Type) y
  : {c : {v:A & χ v} & y = c.1 } <~> (χ y).
    refine (equiv_adjointify _ _ _ _).
    - intros [[c v] p]; simpl in *. destruct p. exact v.
    - intro x. exists (y;x). reflexivity.
    - intro x. reflexivity.
    - intros [[c v] p]; simpl in *; destruct p. reflexivity.
  Defined.

  (** A dependent diagram E over D is equifibered if *)
  Definition equifibered {G:graph} {D:diagram G} (E : dep_diagram D)
    := forall (i j:G) (f:G i j) (u:D i), IsEquiv (E.2 i j f u).

  (** This is actually equivalent to the following *)
  Definition equifibered' {G:graph} {D:diagram G} (E : dep_diagram D)
    := forall (i j:G) (f:G i j) (u:D i),
         IsEquiv ((λ x, (((diagram1 D f u) ; ((E.2 i j f u) x));1)) : E.1 i u -> (∃ (c : ∃ v : D j, E.1 j v), diagram1 D f u = c.1)).

  Lemma equifibered_lemma {G:graph} {D:diagram G} (E : dep_diagram D)
  : (equifibered E) <~> (equifibered' E).
    unfold equifibered, equifibered'.
    refine (equiv_functor_forall' _ _). apply equiv_idmap. intro i.
    refine (equiv_functor_forall' _ _). apply equiv_idmap. intro j.
    refine (equiv_functor_forall' _ _). apply equiv_idmap. intro f.
    refine (equiv_functor_forall' _ _). apply equiv_idmap. intro u.
    simpl.
    refine (equiv_adjointify _ _ _ _).
    - intro H.
      refine (isequiv_adjointify _ _ _ _).
      + intros [[v x] p]. simpl in *. destruct p. exact ((E.2 i j f u)^-1 x).
      + intros [[v x] p]. simpl in *. destruct p. rewrite eisretr. reflexivity.
      + intro x. apply eissect.
    - intro H.
      refine (isequiv_adjointify _ _ _ _).
      + intro x. apply (equiv_inv (IsEquiv := H)). refine (exist _ _ _).
        exists (diagram1 D f u). exact x. reflexivity.
      + intro x. simpl.
        destruct H as [inv retr sect adj]; simpl in *; clear adj. unfold Sect in *.
        specialize (retr ((diagram1 D f u; x); 1)). simpl in retr.
        apply pr1_path in retr.
        
       
  Admitted.
     
End Dependent_diagrams.

Section Descent.

  Context `{ua : Univalence}.
  Context `{fs : Funext}.

  
  (** The the descent theorem holds : "families of type over the colimit of D" is equivalent to "equifibered dependent diagrams over D" *)
  
  Theorem descent {G:graph} {D:diagram G}
  : {E:dep_diagram D & equifibered E} <~> (colimit D -> Type).
    refine (equiv_adjointify _ _ _ _).
    - intros [E Eq].
      refine (colimit_rectnd _ _ _ _ _).
      exact E.1.
      intros i j f c. symmetry.
      refine (path_universe (E.2 i j f c) (feq := _)).
      apply Eq.
    - intro P. refine (exist _ _ _).
      refine (exist _ _ _).
      intros i u. exact (P (colim u)).
      intros i j g u. simpl.
      pose (pp G D i j g u).
      exact (transport idmap (ap P p^)).
      unfold equifibered. intros i j f u.
      exact (isequiv_transport idmap _ _ (ap P (pp G D i j f u)^)). 
    - intros P. simpl.
      apply path_forall.
      refine (colimit_rect _ _ _ _ _).
      intros i x; reflexivity.
      intros i j f x. simpl.
      rewrite transport_paths_FlFr. simpl.
      rewrite (colimit_rectnd_beta_pp). rewrite inv_V.
      rewrite path_universe_transport_idmap.
      rewrite ap_V. rewrite concat_p1. apply concat_Vp.
    - intros [E Eq]. simpl.
      refine (path_sigma' _ _ _).
      apply path_sigma' with 1.
      simpl.
      funext'; intros i j g u v.
      (* apply path_forall; intro i. *)
      (* apply path_forall; intro j. *)
      (* apply path_forall; intro g. *)
      (* apply path_forall; intro u. *)
      (* apply path_forall; intro v. *)
      rewrite ap_V. rewrite colimit_rectnd_beta_pp.
      rewrite inv_V. apply transport_path_universe. 
      apply path_ishprop.
  Defined.                                                                               

  Definition Rezk_P1_diag (G:graph) (D:diagram G) (Y:Type) (X := colimit D) (f : Y -> X) : diagram G.
    refine (Build_diagram _ _ _).
    - intro i. exact (@Pullback X (D i) Y (colim (i := i)) f).
    - intros i j g. simpl. intros [x p].
      exists (diagram1 D g x). exists p.1.
      etransitivity; [|exact p.2].
      apply pp.
  Defined.
  
  Definition Rezk_P1_fun (G:graph) (D:diagram G) (Y:Type) (X := colimit D) (f : Y -> X) (E := Rezk_P1_diag G D Y f) (Y' := colimit E)
  : Y' -> Y.
    refine (colimit_rectnd _ _ _ _ _); simpl.
    + intros i x. exact x.2.1.
    + intros i j φ x; simpl. reflexivity.
  Defined.
      
  Definition Rezk_P1 (G:graph) (D:diagram G) (Y:Type) (X := colimit D) (f : Y -> X) (E := Rezk_P1_diag G D Y f) (Y' := colimit E)
  : IsEquiv (Rezk_P1_fun G D Y f).
    assert ((colimit (Rezk_P1_diag G D Y f)) -> Type).
    { apply (descent (D := (Rezk_P1_diag G D Y f))).
      refine (exist _ _ _).
      refine (exist _ _ _).
      intro i. simpl. intro x. exact (D i).
      intros i j g u X0. simpl. exact (diagram1 D g X0).
      intros i j g u. simpl in *.
    refine (isequiv_adjointify _ _ _ _).
    - pose (p2f(colimit (Rezk_P1_diag G D Y f))).
      unfold p2f in f0. simpl in f0.

      pose (FamequivPow (colimit (Rezk_P1_diag G D Y f))). unfold Fam in e. simpl in e.

      intro y. 
Abort.    
      
  
End Descent.