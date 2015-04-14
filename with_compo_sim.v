Require Import HoTT MyTacs.
Require Import colimit equivalence Peano nat_lemmas.

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
  Admitted.
(*  destruct q as [q pp_q], r as [r pp_r].
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
    Qed.*)
    

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

  Lemma cocone_product_r (X:Type) : cocone_composition pdt_diagram_r X <~> cocone_composition D (A -> X).
     refine (equiv_adjointify _ _ _ _).
    - intros C.
      refine (Build_cocone_composition _ _ _).
      + intros i x a. exact (q C i (x, a)).
      + intros i j f x. simpl. funext a.
        etransitivity; [| exact (H C f (x,a))].
        apply ap. exact (ev_pdt_r _ _ _)^.
      + intros i j k g f x. simpl. try apply path_forall_pp. admit.

    - intros C. refine (Build_cocone_composition _ _ _).
      + intros i z. exact (q C i (fst z) (snd z)).
      + intros i j f z. simpl.
        etransitivity; [refine (ap (λ x, q C j (fst x) (snd x)) (ev_pdt_r _ _ _)) |].
        simpl. refine (ap10 _ _). exact (H C _ _).
      + intros i j k g f x. simpl. hott_simpl. admit.

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

    
  Lemma colimit_product_r {Q: Type} {C: cocone_composition D Q} (HQ: is_colimit_composition C) : is_colimit_composition (pdt_cocone_r C).
    intros X.
    assert (H': map_to_cocone_composition (pdt_cocone_r C) X = ((cocone_product_r X)^-1) o (map_to_cocone_composition C (A -> X)) o ((equiv_uncurry Q _ X)^-1)).
    - funext F.
      refine (path_cocone_composition _ _ _).
      + intros i z. reflexivity.
      + intros i j f z. Abort.


  
        destruct (C.2 i j f (fst z)). simpl.
        reflexivity.
    + rewrite H'. refine isequiv_compose.
      refine isequiv_compose. apply H.
  Defined.

End cocone_product_r.

