Require Import HoTT hit.Coeq Utf8_core.

Context `{fs : Funext}.
Context `{ua : Univalence}.
  

Section Diagram.
  (* From https://github.com/peterlefanulumsdaine/hott-limits *)
  (* Definition 5 *)
  Record graph :=
    { graph0 :> Type;
      graph1 :> graph0 -> graph0 -> Type }.

  Record diagram (G : graph) :=
    { diagram0 :> G -> Type;
      diagram1 :> forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.
  
  Global Arguments diagram0 [G] D i : rename.
  Global Arguments diagram1 [G] D [i j] f x : rename.

  Definition cocone {G:graph} (D:diagram G) (T:Type) :=
    { q : forall i, D i -> T & forall (i j:G) (f: G i j) (x: D i), q j (diagram1 D f x) = q i x}.
  
End Diagram.


Module Export colimit_HIT.
  Private Inductive colimit {G:graph} (D : diagram G) : Type:=
    colim : forall i, (D i -> colimit D).

  Global Arguments colim {G D} {i} x.
  
  Axiom pp : forall (G:graph) (D:diagram G), forall i j:G, forall (f : G i j),
               forall (x:D i), colim (diagram1 D f x) = colim x.

  Definition colimit_ind {G:graph} {D: diagram G} (P : colimit D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q (diagram1 D f x)) = q x)
  : forall w, P w
    := fun w => match w with colim i a => fun _ => q a end pp_q.

  Axiom colimit_ind_beta_pp
  : forall (G:graph) (D: diagram G) (P : colimit D -> Type)
           (q : forall i, forall x, P (colim x))
           (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q _ (diagram1 D f x)) = q _ x)
           (i j:G) (f: G i j) (x: D i),
      apD (@colimit_ind G D P q pp_q) (@pp G D i j f x) = pp_q i j f x.

  Definition colimit_ind_compute (G:graph) (D: diagram G) (P : colimit D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q (diagram1 D f x)) = q x) i (x:D i)
  : colimit_ind P (@q) pp_q (@colim _ _ i x) = q x.
    reflexivity.
  Defined.

  Definition colimit_rec {G : graph} {D:diagram G} (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
  : colimit D -> P.
    refine (colimit_ind _ _ _).
    - exact q.
    - intros i j f x.
      exact ((transport_const (pp G D i j f x) (q _ (diagram1 D f x))) @ (pp_q i j f x)).
  Defined.

  Definition colimit_rec_compute (G : graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
             i (x:D i)
  : colimit_rec P (@q) pp_q (@colim _ _ i x) = @q i x.
    reflexivity.
  Defined.
  
  Definition colimit_rec_beta_pp (G:graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
             (i j:G) (f: G i j) (x: D i)
  : ap (colimit_rec P q pp_q) (@pp G D i j f x) = pp_q i j f x.
    unfold colimit_ind.
    eapply (cancelL (transport_const (pp G D i j f x) _)).
    refine ((apD_const (colimit_ind (λ _ : colimit D, P) q _) (pp G D i j f x))^ @ _).
    refine (colimit_ind_beta_pp G D (λ _, P) q _ i j f x).
  Defined.
End colimit_HIT.


Section colimit_universal_property.
  Definition map_to_cocone {G: graph} {D: diagram G} {P: Type} (q:cocone D P) (X:Type) : (P -> X) -> cocone D X.
    intros f.
    refine (exist _ _ _).
    - intros i x. exact (f (q.1 i x)).
    - intros i j g x. exact (ap f (q.2 i j g x)).
  Defined.

  Definition is_colimit {G: graph} {D: diagram G} {P: Type} (q:cocone D P)
    := forall (X: Type), IsEquiv (map_to_cocone q X).
  
  Theorem colimit_is_colimit (G:graph) (D:diagram G) 
  : is_colimit ((@colim G D); (@pp G D)).
    intro Y; simpl.
    refine (isequiv_adjointify _ _ _ _).
    - intros [q pp_q].
      apply (colimit_rec Y q pp_q).
    - intros [q pp_q]. simpl.
      refine (path_sigma' _ _ _).
      reflexivity.
      simpl.
      repeat (apply path_forall; intro).
      apply colimit_rec_beta_pp.
    - intro φ. simpl.
      apply path_forall. refine (colimit_ind _ _ _).
      intros i x. reflexivity.
      intros i j f x. simpl.
      rewrite transport_paths_FlFr.
      rewrite colimit_rec_beta_pp. hott_simpl.
  Qed.

  
  Definition colimit_equiv (G:graph) (D:diagram G)
    := λ X, BuildEquiv _ _ _ (colimit_is_colimit G D X).

End colimit_universal_property.


Section ColimCoeq.
  Open Scope path.
  
  Variable G : graph.
  Variable X : diagram G.

  Let A := {i : G & {j : G & {f : G i j & X i}}}.
  Let B := {i : G & X i}.

  Let f : A -> B := λ u, (u.2.1; diagram1 X u.2.2.1 u.2.2.2).
  Let g : A -> B := λ u, (u.1; u.2.2.2).

  Let C : cocone X (Coeq f g).
    refine (exist _ _ _).
    intros i x. exact (coeq (i; x)).
    intros i j f0 x; simpl. exact (cp (i; (j; (f0; x)))).
  Defined.

  Goal is_colimit C.
    intros Z. refine (isequiv_adjointify _ _ _ _).
    - intros C'. refine (Coeq_rec _ _ _).
      intros z. exact (C'.1 _ z.2).
      intros z; simpl. exact (C'.2 _ _ _ _).
    - unfold map_to_cocone. intro C'; simpl.
      refine (path_sigma' _ _ _). reflexivity. simpl.
      repeat (apply path_forall; intro).
      match goal with
        |[|- ap (Coeq_rec _ ?cc ?pp) (cp ?bb) = _ ] => set (c := cc); set (p := pp); set (b := bb)
    end.
    refine (@Coeq_rec_beta_cp _ _ f g Z c p b).
    - intro; simpl.
      apply path_forall. refine (Coeq_ind _ _ _).
      intro; simpl. reflexivity.
      intro. simpl.
      rewrite transport_paths_FlFr. hott_simpl.
      rewrite ap_V. rewrite Coeq_rec_beta_cp.
      hott_simpl.
  Defined.
End ColimCoeq.

