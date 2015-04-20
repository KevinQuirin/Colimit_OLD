Require Import MyTacs HoTT.
Require Import cech_nerve colimit colimit2 equivalence Peano nat_lemmas lemmas colimit_CN_base_case.

Context `{fs : Funext}.
Context `{ua : Univalence}.


Section Cocone_composition.

  Inductive generated_function {G: graph} (i k: G) : Type :=
    | G1 : G i k -> generated_function i k
    | Comp : forall (j: G), G j k -> generated_function i j -> generated_function i k.

  Global Arguments G1 [G i j] f : rename.
  Global Arguments Comp [G i k j] g f : rename.

  Notation "g 'O' f" := (Comp g f) (at level 40).

   
  Definition ev {G: graph} {D: diagram G} {i j: G} (f: generated_function i j) : D i -> D j.
    induction f; [exact (diagram1 D g) | exact ((diagram1 D g) o IHf)].
  Defined.

 
  Record cocone_composition {G: graph} (D: diagram G) (X:Type) :=
    { q : forall i, D i -> X;
      H : forall {i j:G} (f: generated_function i j) (x: D i), q j (ev f x) = q i x;
      H2 : forall (i j k:G) (g: G j k) (f: generated_function i j) (x:D i),
             H (g O f) x = (H (G1 g) (ev f x)) @ (H f x) }.
  
  Global Arguments q [G D X] C i x: rename.
  Global Arguments H [G D X] C [i j] f x: rename.
  Global Arguments H2 [G D X] C [i j k] g f x: rename.
  Global Arguments Build_cocone_composition [G D X] q H H2: rename.



Definition path_cocone_composition_naive {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}
           (P := λ qq, forall {i j:G} (f: generated_function i j) (x: D i), qq j (ev f x) = qq i x)
           (Q := λ (qq:forall i, D i -> X), λ (HH: forall (i j:G) (f: generated_function i j) (x: D i), qq j (ev f x) = qq i x), forall (i j k:G) (g: G j k) (f: generated_function i j) (x:D i),
                                       HH _ _ (g O f) x = (HH _ _ (G1 g) (ev f x)) @ (HH _ _ f x))
             (eq0 : q C = q C')
             (eq1 : transport P eq0 (H C) = H C')
             (eq2 : transport _ eq1 (transportD P Q eq0 (H C) (H2 C)) = H2 C')
: C = C' :=
  match eq2 in (_ = v2) return C = {|q := q C'; H := H C'; H2 := v2|} with
    | idpath =>
      match eq1 in (_ = v1) return C = {|q := q C'; H := v1; H2 := eq1 # (transportD P Q eq0 (H C) (H2 C)) |} with
        | idpath =>
          match eq0 in (_ = v0) return C = {|q := v0; H := eq0 # (H C); H2 := transportD P Q eq0 (H C) (H2 C) |} with
            | idpath => idpath
          end
      end
  end.
          


  Definition path1 {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall {i j} f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (i j k:G) (g: G j k) (f: generated_function i j) (x:D i)
  : (H C (g O f) x) @ (eq0 i x) = (eq0 _ (ev (g O f) x)) @ (H C' (G1 g) (ev f x)) @ (H C' f x).
    etransitivity; [refine (whiskerR (H2 C g f x) (eq0 i x)) |].
    etransitivity; [apply concat_pp_p |].
    etransitivity; [refine (whiskerL _ (eq1 _ _ _ _ )) |].
    etransitivity; [apply concat_p_pp |].
    apply whiskerR. refine (eq1 _ _ (G1 g) _).
    Defined.

  Definition path2 {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall {i j} f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (i j k:G) (g: G j k) (f: generated_function i j) (x:D i)
  : (H C (g O f) x) @ (eq0 i x) = (eq0 _ (ev (g O f) x)) @ (H C' (G1 g) (ev f x)) @ (H C' f x).
    etransitivity. apply eq1. etransitivity; [| apply concat_p_pp].
    apply whiskerL. apply H2.
  Defined.

  
    
  Definition path_cocone_composition {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}  
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall i j f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (eq2 : forall i j k g f x, path1 eq0 eq1 i j k g f x = path2 eq0 eq1 i j k g f x)
  : C = C'.
    refine (path_cocone_composition_naive _ _ _).
    - funext i. by apply path_forall.
    - funext i. funext j. funext f. funext x.
      repeat rewrite transport_forall_constant. 
      rewrite transport_paths_FlFr. 
      rewrite concat_pp_p. apply moveR_Vp. 
      rewrite (ap_ap2_path_forall _ _ _ _ eq0 i x).
      rewrite (ap_ap2_path_forall _ _ _ _ eq0 j (ev f x)).
      apply eq1.
    -       
  Admitted.
    

  Definition map_to_cocone_composition {G: graph} {D: diagram G} {X: Type} (C: cocone_composition D X) (Y: Type) (h: X -> Y) : cocone_composition D Y.
    refine (Build_cocone_composition _ _ _).
    - intros i. exact (h o (q C i)).
    - intros i j g x. exact (ap h (H C g x)).
    - intros i j k g f x. simpl.
      etransitivity; [| refine (ap_pp _ _ _)].
      apply ap. refine (H2 C _ _ _).
  Defined.

  
  Definition is_colimit_composition {G: graph} {D: diagram G} {Q: Type} (C: cocone_composition D Q)
    := forall (X:Type), IsEquiv (map_to_cocone_composition C X).

  Lemma IsHProp_is_colimit_composition {G:graph} (D:diagram G) (P:Type) (q: cocone_composition D P)
  : IsHProp (is_colimit_composition q).
    apply trunc_forall.
  Qed.
  
End Cocone_composition.



Section cocone_product_r.

  Variable G: graph.
  Variable D: diagram G.

  Variable A: Type.
  
  Definition pdt_diagram_r : diagram G.
    refine (Build_diagram _ _ _).
    + intros i. exact ((D i) * A).
    + simpl. intros i j f x. exact (diagram1 D f (fst x), snd x).
  Defined.
 
  Definition pdt_cocone_r {Q: Type} (C: cocone_composition D Q) : cocone_composition pdt_diagram_r (Q * A).
    refine (Build_cocone_composition _ _ _); simpl.
    - intros i z. exact (q C i (fst z) , snd z).
    - intros i j f z. induction f; simpl.
      * exact (path_prod' (H C (G1 g) (fst z)) 1).
      * etransitivity; [|apply IHf]. refine (ap (λ x, (x, _)) _).
        exact (H C (G1 g) _).
    - intros i j k g f x. induction f; hott_simpl.
  Defined.

  
  Lemma ev_pdt_r {i j: G} (f: generated_function i j) (x: D i) (a: A)
  : ev f (D := pdt_diagram_r) (x, a) = (ev f x, a).
    induction f; [reflexivity | simpl].
    exact (ap (λ z, (diagram1 D g (fst z), snd z)) IHf).
  Defined.

  (*
  Lemma cocone_product_r (X:Type) : cocone_composition pdt_diagram_r X <~> cocone_composition D (A -> X).
     refine (equiv_adjointify _ _ _ _).
    - intros C.
      refine (Build_cocone_composition _ _ _).
      + intros i x a. exact (q C i (x, a)).
      + intros i j f x. simpl. funext a.
        etransitivity; [| exact (H C f (x,a))].
        apply ap. exact (ev_pdt_r _ _ _)^.
      + intros i j k g f x. simpl.
        etransitivity; [|apply path_forall_pp].
        apply ap. funext a.
        rewrite (inverse_ap (λ z : D j ∧ A, (diagram1 D g (fst z), snd z)) (ev_pdt_r f x a)).
        rewrite <- (ap_compose (λ z : D j ∧ A, (diagram1 D g (fst z), snd z)) (q C k) (ev_pdt_r f x a)^).
        hott_simpl. rewrite (H2 C). hott_simpl. apply whiskerR.
        exact (concat_Ap (H C (G1 g)) (ev_pdt_r f x a)^).
    - intros C. refine (Build_cocone_composition _ _ _).
      + intros i z. exact (q C i (fst z) (snd z)).
      + intros i j f z. simpl.
        etransitivity; [refine (ap (λ x, q C j (fst x) (snd x)) (ev_pdt_r _ _ _)) |].
        simpl. refine (ap10 _ _). exact (H C _ _).
      + intros i j k g f x. simpl. unfold ev_pdt_r. hott_simpl.
        match goal with
            [|- (ap ?gg (ap ?ff ?FF)) @ ap10 _ _ =  ((ap10 _ _) @ ap _ ?FF) @ ap10 _ _
            ] => set (F := FF); set (f' := ff); set (g' := gg); rewrite <- (ap_compose f' g' F)
        end.
        repeat rewrite <- (ap_apply_l).
        rewrite (H2 C). rewrite ap_pp. 
        hott_simpl. apply whiskerR.
        etransitivity. apply (concat_Ap (ap (λ f0 : A → X, f0 (snd x))) F).
      rewrite
        rewrite <- ap_concat.


                    ap10_ap_precompose:
  ∀ (A B C : Type) (f : A → B) (g g' : B → C) (p : g = g') 
  (a : A), ap10 (ap (λ h : B → C, h o f) p) a = ap10 p (f a)
ap10_ap_postcompose:
  ∀ (A B C : Type) (f : B → C) (g g' : A → B) (p : g = g') 
  (a : A), ap10 (ap (λ h : A → B, f o h) p) a = ap f (ap10 p a)
ap11_is_ap10_ap01:
  ∀ (A B : Type) (f g : A → B) (h : f = g) (x y : A) 
  (p : x = y), ap11 h p = ap10 h x @ ap g p
        set (CC := (generated_function_rect G i
           (λ (j0 : G) (f0 : generated_function i j0),
            ev f0  (D := pdt_diagram_r) (fst x, snd x) = (ev f0 (fst x), snd x))
           (λ (k0 : G) (g0 : G i k0), idpath)
           (λ (k0 j0 : G) (g0 : G j0 k0) (f0 : generated_function i j0)
            (IHf : ev f0  (D := pdt_diagram_r) (fst x, snd x) = (ev f0 (fst x), snd x)),
            ap (λ z : D j0 ∧ A, (diagram1 D g0 (fst z), snd z)) IHf) j f)) in *.
        admit.

    - intros C. refine (path_cocone_composition _ _ _); simpl.
      + intros i x. reflexivity.
      + intros i j f x. simpl. hott_simpl.
        match goal with
          | [|- path_forall _ _ (λ a, _ @ (_ @ ?CC)) = _] => transitivity (path_forall _ _ (λ a, CC))
        end.
        apply ap. funext a. hott_simpl.
        match goal with
          | [|- ?CC1 @ ?CC2 @ ?CC3 = _] => transitivity (CC2^ @ CC2 @ CC3); [refine (ap (λ C, C @ CC2 @ CC3) _) | hott_simpl]
        end. refine (inverse_ap (λ z : D j ∧ A, q C j (fst z) (snd z)) (ev_pdt_r f x a))^.
        apply eta_path_forall.
      + admit.

    - intros C. refine (path_cocone_composition _ _ _); simpl.
      + intros i z. reflexivity.
      + intros i j f [x a]. unfold path_forall.
        rewrite eisretr. simpl. hott_simpl.
        rewrite <- inverse_ap.
        admit.
      + admit.
  Defined.
*)

    
  Lemma colimit_product_r {Q: Type} {C: cocone_composition D Q} (HQ: is_colimit_composition C) : is_colimit_composition (pdt_cocone_r C).
Admitted.
    (*    intros X.
    assert (H': map_to_cocone_composition (pdt_cocone_r C) X = ((cocone_product_r X)^-1) o (map_to_cocone_composition C (A -> X)) o ((equiv_uncurry Q _ X)^-1)).
    - funext F.
      refine (path_cocone_composition _ _ _).
      + intros i z. reflexivity.
      + intros i j f z.
  
        destruct (C.2 i j f (fst z)). simpl.
        reflexivity.
    + rewrite H'. refine isequiv_compose.
      refine isequiv_compose. apply H.
  Defined.
*)
End cocone_product_r.





Section TheProof.

  
  Variable (A:Type).
  Let D := prod_diag A.
  Variable Q : Type.
  Variable C : cocone_composition D Q.
  Variable (colimQ : is_colimit_composition C).
  
  Let pi := @snd Q A.

  Lemma le_1_Sn (n:nat) : 1 <= S n.
    induction n. auto.
    apply le_S. exact IHn.
  Qed.

  Lemma isequiv_snd_QA
  : IsEquiv (pi : Q ∧ A -> A).
    refine (isequiv_adjointify _ _ _ _).
    - exact (λ x, (q C 0 (x, tt), x)).
    - intros x. reflexivity.
    - intros x. apply path_prod; [simpl|reflexivity].
      generalize x; apply ap10.
      specialize (colimit_product_r _ _ A colimQ); intros colimQA. unfold is_colimit in *.
      refine (equiv_inj (map_to_cocone_composition (pdt_cocone_r _ _ A C) Q) _). shelve.
      refine (path_cocone_composition _ _ _).
      + intros i [[z z'] a]. simpl in *.
        induction i.
        * destruct z'; simpl. 
          etransitivity. exact (H C (@G1 Cech_nerve_graph 1 0 (idpath,(1; le_n 1))) (a, (z, tt))).
          exact (H C (@G1 Cech_nerve_graph 1%nat 0 (idpath,(0; le_0 _))) (a, (z, tt)))^. 
        * etransitivity; [exact (IHi (snd z')) |].
          etransitivity; [| exact (H C (@G1 Cech_nerve_graph (i.+1) i (idpath,(1%nat; le_1_Sn _))) (z,z'))].
          apply ap. refine (path_prod _ _ _ _). reflexivity.
          destruct i; [apply path_ishprop | reflexivity].
      + induction i; intros j f; induction f. destruct g as [f [q Hq]]. shelve. destruct f; simpl. intros u.
        Admitted. (*
        match goal with
            |[|- ?PP @ _ = _] => assert (X : 1 = PP)
          end.
        { unfold path_prod'. simpl.
          rewrite (ap_compose pi (λ x, C.1 0 (x,tt))).
          unfold pi. rewrite ap_snd_path_prod. reflexivity. }
        destruct X; rewrite concat_1p.
        match goal with
            |[|- _ = _ @ ?PP] => assert (X : (C.2 j.+1 j (1, (q; Hq)) (fst u)) = PP)
          end.
          { unfold path_prod'. simpl.
            rewrite ap_fst_path_prod. reflexivity. }
          destruct X.

        induction j; simpl.
        * destruct u as [[u1 [u2 u]] v]. simpl in *.
          destruct u. 
          destruct (le_1_is_01 q Hq).
          symmetry in p; destruct p. simpl.
          assert (X : 1 = (path_ishprop tt tt)).
          { apply path_ishprop. }
          destruct X. simpl; rewrite concat_1p.
          assert (X : le_0 1 = Hq).
          { refine (path_ishprop _ _). apply IsHProp_le. }
          destruct X.
          apply moveR_pM.
          rewrite concat_pp_p.
          pose (C.2 1%nat 0 (1, (1%nat; le_n 1)) (v, (u1, tt))). simpl in p.
          pose ((C.2 1%nat 0 (1, (0; le_0 1)) (v, (u1, tt)))^). simpl in p0.
          admit.
          symmetry in p; destruct p; simpl.
          admit.
        * 


        admit.
  Defined.
*)


    
  
End TheProof.
