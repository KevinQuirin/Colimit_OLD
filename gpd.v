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

Section Colimit_Gpd.

  
  (* Lemma transport_hfiber {X Y:Type} (f:X -> Y) (y z:Y) (a:hfiber f y) (b:hfiber f z) (p:y=z) (q:p # a = b) *)
  (* : transport (λ u:Y, hfiber f u) p a = b. *)
  (* Proof. *)
  (*   pose (@transport_sigma' Y X (λ y x, f x = y) y z p a); simpl in p0. *)
    
  (*   destruct p. simpl. exact q. Defined. *)
  
  Local Notation T f i := (Gpd_aux f i).1.
  Local Notation α f i := (Gpd_aux f i).2.

  Variables X Y:Type. Variable f:X -> Y.
  Local Notation Tf i := (T f i).
  Local Notation αf i := (α f i).

  Lemma bar (T:Type) (A B: T -> Type) (g h:forall y:T, A y -> B y) (y z:T) (p:y=z)
    : forall (b:B y) (b':B z) (q: p # b = b'), transport (λ u, Coeq (g u) (h u)) p (@coeq _ _ (g y) (h y) b) = @coeq _ _ (g z) (h z) b'.
  Proof.
    intros b b'.
    destruct p. simpl.
    exact (ap coeq).
  Defined.

  
  Lemma foo : {y:Y & T (λ x:hfiber f y, tt) 1} <~> T f 1.
  Proof.
    assert (X0 : (∃ y : Y, T (λ _ : hfiber f y, tt) 1) <~> (∃ y : Y, Coeq (fst : (hfiber f y)*(hfiber f y) -> _) snd)).
    refine (equiv_functor_sigma_id _).
    intro a. simpl.
    refine (equiv_adjointify _ _ _ _).
    refine (functor_coeq _ _ _ _).
    exact (λ x, (x.1,x.2.1)).
    exact idmap.
    intro; reflexivity.
    intro; reflexivity.
    refine (functor_coeq _ _ _ _).
    exact (λ x, (fst x; (snd x; 1))).
    exact idmap.
    intro; reflexivity.
    intro; reflexivity.
    refine (functor_coeq_sect _ _ _ _ _ _ _ _ _ _ _ _).
    intro; reflexivity.
    intro; reflexivity.
    intro; reflexivity.
    intro; reflexivity.
    refine (functor_coeq_sect _ _ _ _ _ _ _ _ _ _ _ _).
    intro x; simpl.
    apply path_sigma' with 1. simpl. apply path_sigma' with 1. simpl. apply path_ishprop.
    intro; reflexivity.
    intros [b [c p]]. simpl. rewrite concat_1p.
    assert (d : 1 = p) by apply path_ishprop; destruct d.
    match goal with
    |[|- ap _ (_ _ _ (_ _ _ ?xx)) = _ ] => assert (rew : 1 = xx) by apply path_ishprop; destruct rew
    end.
    reflexivity.

    intros [b [c p]]. simpl. rewrite concat_1p.
    assert (d : 1 = p) by apply path_ishprop; destruct d.
    match goal with
    |[|- ap _ (_ _ _ (_ _ _ ?xx)) = _ ] => assert (rew : 1 = xx) by apply path_ishprop; destruct rew
    end.
    reflexivity.
    
    etransitivity; [exact X0 | idtac]; clear X0.
    
    refine (equiv_adjointify _ _ _ _).
    - intros [y p]; simpl in *.
      revert p. refine (functor_coeq _ _ _ _).
      intros p. exists (fst p).1. exists (snd p).1.
      exact ((fst p).2 @ (snd p).2^).
      exact pr1.
      intro; reflexivity.
      intro; reflexivity.
    - refine (Coeq_rec _ _ _).
      simpl. intro x.
      exact (f x; coeq (x;1)).
      intros p; simpl in *.
      apply path_sigma' with p.2.2.     
      etransitivity; [idtac | exact (@cp _ _ (fst : (hfiber f (f p.2.1))*(hfiber f (f p.2.1)) -> _) snd ((p.1;p.2.2), (p.2.1;1)))]. cbn.

      apply (@bar Y (λ y, (hfiber f y)*(hfiber f y)) (λ y, hfiber f y) (λ _, fst) (λ _, snd) (f p.1) (f p.2.1) p.2.2 (p.1;1) (p.1;p.2.2)).
      abstract (
          pose (@transport_sigma' Y X (λ y x, f x = y) (f p.1) (f p.2.1) p.2.2 (p.1;1)); simpl in p0;
          rewrite transport_paths_FlFr in p0; simpl in p0;
          rewrite ap_const in p0; rewrite ap_idmap in p0;
          simpl in p0; rewrite concat_1p in p0; exact p0 ).
      
    - cbn.
      refine (Coeq_ind _ _ _).
      intro a. reflexivity.
      cbn. intros [a [b p]].
      rewrite transport_paths_FlFr.
      rewrite ap_idmap.
      cbn.

End Colimit_Gpd.