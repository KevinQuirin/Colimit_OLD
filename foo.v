Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.
Require Import equivalence lemmas colimit cech_nerve nat_lemmas.

Module Export LoopSpace.
  
  Private Inductive LoopSpace (X:Type@{i}) : Type@{i} :=
|Point : LoopSpace X.

  Axiom Loop : forall {X:Type}, X -> (Point X = Point X).

  Definition LoopSpace_ind (X:Type) (P : LoopSpace X -> Type)
             (H_P : P (Point X))
             (H_Loop : forall x:X, (Loop x) # H_P = H_P)
  : forall (y:LoopSpace X), P y
    := fun y => (match y return (_ -> P y)
                 with Point => (fun _ => H_P) end) H_Loop.

  Axiom LoopSpace_comp_Loop : forall (X:Type) (P : LoopSpace X -> Type)
             (H_P : P (Point X))
             (H_Loop : forall x:X, (Loop x) # H_P = H_P)
             (x:X),
                                apD (LoopSpace_ind X P H_P H_Loop) (Loop x) = H_Loop x.

End LoopSpace.

Definition LoopSpace_rec (X Y:Type) (H_P : Y) (H_Loop : X -> H_P = H_P)
: LoopSpace X -> Y.
  apply (LoopSpace_ind X (λ _, Y) H_P).
  intros x. exact (transport_const _ _ @ H_Loop x).
Defined.

Definition LoopSpace_comp_nd_Loop (X Y : Type)
  (H_P : Y) (H_Loop : X -> H_P = H_P) (x:X)
: ap (LoopSpace_rec X Y H_P H_Loop) (Loop x) = H_Loop x.
Proof.
  apply (cancelL (transport_const (Loop x) H_P)).
  transitivity (apD (LoopSpace_rec X Y H_P H_Loop) (Loop x)).
  symmetry; refine (apD_const (LoopSpace_rec X Y H_P H_Loop) _).
  refine (LoopSpace_comp_Loop X (fun _ : LoopSpace X => Y) H_P _ x).
Defined.

Definition LoopSpace_comp (X Y:Type) (H_P : Y) (H_Loop : X -> H_P = H_P)
: LoopSpace_rec X Y H_P H_Loop (Point X) = H_P.
  reflexivity.
Defined.

Definition LoopSpace_eta `{fs : Funext} (X:Type) (P:LoopSpace X -> Type) (f:forall y, P y)
: f = LoopSpace_ind X P (f (Point X)) (λ x, apD f (Loop x)).
  apply path_forall.
  unfold pointwise_paths.
  refine (LoopSpace_ind X
                        (λ x, f x = LoopSpace_ind X P (f (Point X)) (λ x0 : X, apD f (Loop x0)) x)
                        idpath _).
  intro x.
  refine (transport_paths_FlFr_D
    (g := LoopSpace_ind X P (f (Point X)) (λ x, apD f (Loop x)))
    _ _ @ _); simpl.
  apply moveR_pM. apply (concat (concat_p1 _)), (concatR (concat_1p _)^).
  apply ap, inverse. refine (LoopSpace_comp_Loop _ _ _ _ _).
Defined.

Section Foo.

  Context `{ua : Univalence}.
  Context `{fs : Funext}.

  Definition Unit_to_BX (X:Type) (BX := LoopSpace X) : Unit -> BX
    := λ tt, Point X.

  Definition CN_BX (X:Type) (BX := LoopSpace X) := Cech_nerve_diagram (Unit_to_BX X).

  Definition cone_morphism (G:graph) (D: diagram G) (X:Type) (q r: forall i, D i -> X) (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x) (pp_r : forall (i j:G) (f: G i j) (x: D i), r _ (diagram1 D f x) = r _ x)
             (eq_qr : forall i, q i == r i)
             (eq_pp_qr : forall i j f x, pp_q i j f x @ eq_qr i x = eq_qr j (diagram1 D f x) @ pp_r i j f x)
  : (existT (λ qq : forall i, D i -> X, forall (i j:G) (f: G i j) (x: D i), qq j (diagram1 D f x) = qq i x) q pp_q) = (r;pp_r).
    refine (path_sigma' _ (path_forall _ _ (λ i, path_forall _ _ (eq_qr i))) _). simpl.
    apply path_forall; intro i.
    apply path_forall; intro j.
    apply path_forall; intro f.
    apply path_forall; intro x.

    repeat rewrite transport_forall_constant.
    rewrite transport_paths_FlFr. simpl.
    rewrite concat_pp_p. apply moveR_Vp. simpl.
    rewrite (ap_ap2_path_forall (λ u, D u) (λ _, λ _, X) q r eq_qr i x).
    rewrite (ap_ap2_path_forall (λ u, D u) (λ _, λ _, X) q r eq_qr j (diagram1 D f x)).
    apply eq_pp_qr.
  Qed.

  Definition cocone (G:graph) (D:diagram G) (T:Type) :=
    {q : forall i, D i -> T & forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x}.

 Definition colimit_unicity (G:graph) (D: diagram G) (P Q:Type) (q : forall i, D i -> P) (r : forall i, D i -> Q) (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x) (pp_r : forall (i j:G) (f: G i j) (x: D i), r _ (diagram1 D f x) = r _ x)
             (colimX : is_colimit G D P q pp_q)
             (colimY : is_colimit G D Q r pp_r)
 : P <~> Q.
   unfold is_colimit in *.
   pose (φP := λ X:Type, (λ f : P → X,
              (λ (i : G) (x : D i), f (q i x);
              λ (i j : G) (g : G i j) (x : D i), ap f (pp_q i j g x)))). simpl in φP.
   
    refine (equiv_adjointify _ _ _ _).
    - exact (equiv_inv (IsEquiv := (colimX Y)) (r;pp_r)).
    - exact (equiv_inv (IsEquiv := (colimY X)) (q;pp_q)).
    - intro y.
      match goal with
        |[|- ?ggg ?rrr (?fff ?qqq _) = _] =>
         set (g := ggg); set (f := fff); set (rr := rrr); set (qq := qqq)
      end.
      set (ff := f qq). set (gg := g rr).
      revert y.
      refine (ap10 (f := gg o ff) (g:=idmap) _).
      refine (@equiv_inj _ _ _ (colimY Y) _ _ _).

      refine (cone_morphism _ _ _ _ _ _ _ _ _).
      + intros i x.
        etransitivity; [simpl | exact (ap10 (apD10 (eisretr _ (IsEquiv := colimX Y) (r;pp_r))..1 i) x)]. simpl.
        apply ap.
        exact (ap10 (apD10 (eisretr _ (IsEquiv := colimY X) (q;pp_q))..1 i) x).
      + simpl. intros i j φ x.
        rewrite ap_idmap.
        rewrite ap_compose.
        unfold ff, gg, qq, rr, f, g. simpl.
        clear ff; clear gg; clear qq; clear rr; clear f; clear g.
        unfold equiv_inv.
        match goal with
          |[|- ap ?fff (ap ?ggg _) @ (ap _ _ @ _) = _] => set (f := fff); set (g := ggg)
        end.
        repeat rewrite concat_p_pp.
        apply moveR_pM.
        repeat rewrite concat_pp_p.
        apply moveL_Mp.

        rewrite <- ap_pp.
        rewrite <- ap_V.
        rewrite <- ap_pp.
        repeat rewrite <- ap10_ap_precompose.
        rewrite 
        
        match goal with
          |[|- ?PP1 @ (?PP2 @ ?PP3) = ?QQ1 @ (?QQ2 @ ?QQ3)] =>
           set (P1 := PP1);
             set (P2 := PP2);
             set (P3 := PP3);
             set (Q1 := QQ1);
             set (Q2 := QQ2);
             set (Q3 := QQ3)
        end. simpl in *.
                                                           

  Qed.
      
  
  Lemma BX_colimit_CN_BX (G:Type) (BG := LoopSpace G)
  : is_colimit (Cech_nerve_graph)
               (CN_BX G)
               BG
               (Cech_nerve_commute (Unit_to_BX G))
               (Cech_nerve_pp (Unit_to_BX G)).
    intro X.
    refine (isequiv_adjointify _ _ _ _).
    - intros [qq p_qq].
      refine (LoopSpace_rec G X _ _).
      apply (qq 0).
      simpl. exact ((tt,tt);tt).
      intro x.
      pose (e1 := p_qq 1 0 (idpath,(1;le_n 1)) ((tt,(tt,tt));(Loop x, tt))).
      pose (e2 := p_qq 1 0 (idpath,(0;(le_S _ _ (le_n 0)))) ((tt,(tt,tt));(Loop x, tt))).
      exact (e1 @ e2^).
      (* reflexivity. *)
    - intros [qq p_qq].

      refine (cone_morphism _ _ _ _ _ _ _ _ _).
      + intros i x.  simpl.
      induction i.
      destruct x as [[x1 x2] x3]; destruct x1, x2, x3.
      reflexivity.
      exact ((IHi (snd x.1; snd x.2)) @ (p_qq i.+1 i (idpath,(0;le_0 (i.+1))) x)).
      + intros i j [f [q Hq]] x. destruct f; simpl.

        match goal with
          |[|- ap _ ?pp @ _ = _ ] => set (foo := pp)
        end. simpl in foo.
        unfold Unit_to_BX in foo; simpl in foo.
        induction j. simpl. simpl in x.

        destruct (le_1_is_01 q Hq).
        symmetry in p; destruct p. simpl.
        admit.

        
        admit.
        admit.

    
    - intro φ.
      simpl. unfold Cech_nerve_commute, Unit_to_BX, LoopSpace_rec.
      pose (LoopSpace_eta G (λ _ : LoopSpace G, X) φ)^.
      path_via (LoopSpace_ind G (λ _ : LoopSpace G, X) (φ (Point G))
                              (λ x : G, apD φ (Loop x))).
      apply ap. apply path_forall; intro x.
      rewrite apD_const. hott_simpl.
      
  Qed.
      
End Foo.