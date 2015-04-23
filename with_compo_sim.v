Require Import MyTacs HoTT.
Require Import cech_nerve colimit colimit2 equivalence Peano nat_lemmas lemmas colimit_CN_base_case.

Context `{fs : Funext}.
Context `{ua : Univalence}.


Section Cocone_composition.

  Inductive G2 {G: graph} (i k: G) : Type :=
    | G21 : G i k -> G2 i k
    | G22 : forall (j: G), G j k -> G i j -> G2 i k.

  Global Arguments G21 [G i j] f : rename.
  Global Arguments G22 [G i k j] g f : rename.

  Notation "g 'O' f" := (G22 g f) (at level 40).

   
  Definition ev {G: graph} {D: diagram G} {i j: G} (f: G2 i j) : D i -> D j.
    induction f; [exact (diagram1 D g) | exact ((diagram1 D g) o (diagram1 D g0))].
  Defined.

 
  Record cocone_composition {G: graph} (D: diagram G) (X:Type) :=
    { q : forall i, D i -> X;
      H : forall {i j:G} (f: G2 i j) (x: D i), q j (ev f x) = q i x;
      H2 : forall (i j k:G) (g: G j k) (f: G i j) (x:D i),
             H (g O f) x = (H (G21 g) (diagram1 D f x)) @ (H (G21 f) x) }.
  
  Global Arguments q [G D X] C i x: rename.
  Global Arguments H [G D X] C [i j] f x: rename.
  Global Arguments H2 [G D X] C [i j k] g f x: rename.
  Global Arguments Build_cocone_composition [G D X] q H H2: rename.



(*
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
*)

  Definition path1 {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall {i j} f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (i j k:G) (g: G j k) (f: G i j) (x:D i)
  : (H C (g O f) x) @ (eq0 i x) = (eq0 _ (ev (g O f) x)) @ (H C' (G21 g) (diagram1 D f x)) @ (H C' (G21 f) x).
    etransitivity; [refine (whiskerR (H2 C g f x) (eq0 i x)) |].
    etransitivity; [apply concat_pp_p |].
    etransitivity; [refine (whiskerL _ (eq1 _ _ _ _ )) |].
    etransitivity; [apply concat_p_pp |].
    apply whiskerR. refine (eq1 _ _ (G21 g) _).
    Defined.

  Definition path2 {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall {i j} f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (i j k:G) (g: G j k) (f: G i j) (x:D i)
  : (H C (g O f) x) @ (eq0 i x) = (eq0 _ (ev (g O f) x)) @ (H C' (G21 g) (diagram1 D f x)) @ (H C' (G21 f) x).
    etransitivity. apply eq1. etransitivity; [| apply concat_p_pp].
    apply whiskerL. apply H2.
  Defined.
    
  Definition path_cocone_composition {G: graph} {D: diagram G} {X:Type} {C C': cocone_composition D X}  
             (eq0 : forall i, q C i == q C' i)
             (eq1 : forall i j f x, (H C f x) @ (eq0 i x) = (eq0 j (ev f x)) @ (H C' f x))
             (eq2 : forall i j k g f x, path1 eq0 eq1 i j k g f x = path2 eq0 eq1 i j k g f x)
  : C = C'.
(*    refine (path_cocone_composition_naive _ _ _).
    - funext i. by apply path_forall.
    - funext i. funext j. funext f. funext x.
      repeat rewrite transport_forall_constant. 
      rewrite transport_paths_FlFr. 
      rewrite concat_pp_p. apply moveR_Vp. 
      rewrite (ap_ap2_path_forall _ _ _ _ eq0 i x).
      rewrite (ap_ap2_path_forall _ _ _ _ eq0 j (ev f x)).
      apply eq1.
    -       *)
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

End Cocone_composition.



Section cocone_product_r.

  Variable G: graph.
  Variable D: diagram G.

  Variable A: Type.
  
 
  Definition pdt_cocone_r {Q: Type} (C: cocone_composition D Q) : cocone_composition (pdt_diagram_r D A) (Q * A).
    refine (Build_cocone_composition _ _ _); simpl.
    - intros i z. exact (q C i (fst z) , snd z).
    - intros i j f z. destruct f; simpl.
      * exact (path_prod' (H C (G21 g) (fst z)) 1).
      * refine (path_prod' _ 1). etransitivity. exact (H C (G21 g) _).
        exact (H C (G21 g0) _).
    - intros i j k g f x. simpl. hott_simpl.
      exact (path_prod_pp (q C k (@diagram1 _ D j k g (@diagram1 _ D i j f (fst x))), snd x)
        (q C j (@diagram1 _ D i j f (fst x)), snd x) (q C i (fst x), snd x)
        (H C (G21 g) (@diagram1 _ D i j f (fst x))) (H C (G21 f) (fst x)) 1 1).
  Defined.

    
  Lemma colimit_product_r {Q: Type} {C: cocone_composition D Q} (HQ: is_colimit_composition C) : is_colimit_composition (pdt_cocone_r C).
Admitted.

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
          etransitivity. exact (H C (@G21 Cech_nerve_graph 1 0 (idpath,(1; le_n 1))) (a, (z, tt))).
          exact (H C (@G21 Cech_nerve_graph 1%nat 0 (idpath,(0; le_0 _))) (a, (z, tt)))^. 
        * etransitivity; [exact (IHi (snd z')) |].
          etransitivity; [| exact (H C (@G21 Cech_nerve_graph (i.+1) i (idpath,(1%nat; le_1_Sn _))) (z,z'))].
          apply ap. refine (path_prod _ _ _ _). reflexivity.
          destruct i; simpl. shelve. reflexivity.
      + induction i; intros j f; induction f. destruct g as [f [q Hq]]. 
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
