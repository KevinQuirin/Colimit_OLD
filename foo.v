(*Require Export Utf8_core.
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

  (* We prove here that we can use the real diagram A×...×A -> ... -> A×A -> A instead of the Cech nerve of tr with irrelevant second compenents *)
  
  Lemma ishprop_pullback_tr_pr2
        (A : Type)
        (i : nat)
        (x : ∃ P : A ∧ hProduct A i, char_hPullback (λ a : A, tr (n:=-1) a) i P)
  : IsHProp
      (char_hPullback (λ a : A, tr (n:=-1) a) i (let (proj1_sig, _) := x in proj1_sig)).
    induction i; simpl.
    apply true_ishprop.
    refine (trunc_prod). simpl in *.
    exact (IHi (snd x.1; snd x.2)).
  Qed.

  Definition prod_diag (A:Type) : diagram Cech_nerve_graph.
    refine (Build_diagram _ _ _).
    - simpl. intro i. exact (hProduct A (S i)).
    - simpl. intros i j [f q]. destruct f. intros x.
      exact (forget_hProduct A (S j) x q).
  Defined.

  Definition CN_tr_cocone (A:Type)
  : cocone (Cech_nerve_diagram (λ a:A, tr (n:=-1) a)) (colimit (prod_diag A)).
    refine (exist _ _ _); simpl.
    - intros i X.
      apply (@colim (Cech_nerve_graph) _ i). exact X.1.
    - intros i j [f [q Hq]] x; destruct f; simpl.
      exact (pp (Cech_nerve_graph) (prod_diag A) (j.+1) j (idpath,(q;Hq)) x.1).
  Defined.

  Lemma inhab_pullback_tr_pr2 (A:Type) (i:nat)
  : forall x:A*(hProduct A i), char_hPullback (λ a : A, tr (n:=-1) a) i x.
    intro x.
    induction i. exact tt. simpl.
    refine (pair _ _).
    apply path_ishprop.
    apply IHi.
  Qed.

  Lemma colim_prod_diag_CN_tr (A:Type)
  : is_colimit (Cech_nerve_diagram (λ a:A, tr (n:=-1) a)) (colimit (prod_diag A)) (CN_tr_cocone A).
    refine (transport_is_colimit (Cech_nerve_graph) (prod_diag A) _ _ _ _ _ _ _ _ _ _ (colimit_is_colimit _ (prod_diag A))); simpl.
    - intro i. refine (equiv_adjointify _ _ _ _).
      + intros x. exists x. apply inhab_pullback_tr_pr2.
      + exact pr1.
      + intros x. apply path_sigma' with idpath.
        simpl. refine (path_ishprop _ _). apply ishprop_pullback_tr_pr2.
      + intros x. reflexivity.
    - intros i j [f [q Hq]]; destruct f; simpl.
      intro x; reflexivity.
    - reflexivity.
    - simpl.
      apply path_forall; intro i.
      apply path_forall; intro j.
      apply path_forall; intros [f [q Hq]]; destruct f.
      apply path_forall; intro x. simpl. hott_simpl.
      unfold path_sigma'.
      pose (p := @pr1_path_sigma). unfold pr1_path in p. rewrite p.
      hott_simpl.
  Qed.

    
      
End Foo.*)