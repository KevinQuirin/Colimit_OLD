Require Import Utf8_core.
Require Import HoTT.
Require Import equivalence cech_nerve colimit colimit2.
Require Import Peano nat_lemmas.

Context `{fs : Funext}.
Context `{ua : Univalence}.

Section Cocone_composition.

  Inductive generated_function {G: graph} (i k: G) : Type :=
    | G1 : G i k -> generated_function i k
    | Comp : forall (j: G), G j k -> generated_function i j -> generated_function i k.

  Global Arguments G1 [G i j] f : rename.
  Global Arguments Comp [G i k j] g f : rename.
  
  Definition ev {G: graph} {D: diagram G} {i j: G} (f: generated_function i j) (x: D i) : D j.
    induction f; [exact (diagram1 D g x) | exact (diagram1 D g (IHf))].
  Defined.
  
  (* ça unifie pas... *)
  Record cocone_composition {G: graph} (D: diagram G) (X:Type) :=
    { q : forall i, D i -> X;
      H : forall {i j:G} (f: generated_function i j) (x: D i), q j (ev f x) = q i x;
      H2 : forall (i j k:G) (g: G j k) (f: generated_function i j) (x:D i),
             (* @paths (q k (diagram1 D g (ev f x)) = q i x) *)
                    (H (Comp g f) x) =
                    ((H (G1 g) (ev f x)) @ (H f x)) }.



             (* H (Comp g f) x = (H (G1 g) (ev f x)) @ (H f x) }. *)









































  
  Global Arguments cocone_q [G D T] C i x: rename.
  Global Arguments cocone_p [G D T] C [i j] f x: rename.
  Global Arguments cocone_pp [G D T] C [i j k] f g x: rename.

  Definition map_to_cocone_composition {G:graph_composition} (D:diagram_composition G) (P:Type) (q: cocone_composition D P) (X:Type) (f: P -> X) : cocone_composition D X.
    refine (Build_cocone_composition _ _ _ _ _ _).
    - intros i x. exact (f (cocone_q q i x)).
    - intros i j g x. exact (ap f (cocone_p q g x)).
    - intros i j k f0 g x. simpl.
      etransitivity; [refine (ap_pp _ _ _)^ | idtac].
      apply (transport (λ U, _ = U @ _) (ap_compose (λ x0, (cocone_q q k x0)) f _)^).
      etransitivity; [idtac | refine (ap_pp _ _ _)].
      apply ap.
      apply cocone_pp.
  Defined.
  
End Cocone_composition.

Section IsColimit_composition.

  Definition is_colimit_composition {G:graph_composition} (D:diagram_composition G) (P:Type) (q: cocone_composition D P)
    := forall (X:Type), IsEquiv (map_to_cocone_composition D P q X).

  Lemma IsHProp_is_colimit_composition {G:graph_composition} (D:diagram_composition G) (P:Type) (q: cocone_composition D P)
  : IsHProp (is_colimit_composition D P q).
    apply trunc_forall.
  Qed.
  
End IsColimit_composition.

Section Cech_nerve.

  Definition Cech_nerve_graph : graph_composition.
    refine (Build_graph_composition _ _ _).
    - exact nat.
    - intros m n.
      exact ((S n = m) /\ (nat_interval m)).
    - intros x y z f g. simpl in *.
      
  
End Cech_nerve.

Module Export colimit_composition.

  Private Inductive colimit_composition {G:graph_composition} (D : diagram_composition G) : Type :=
    inc : forall i, (D i -> colimit_composition D).

  Global Arguments inc {G D} {i} x.
  
  Axiom glue : forall (G:graph_composition) (D:diagram_composition G), forall i j:G, forall (f : G i j),
               forall (x:D i), inc (diagram1 D f x) = inc x.
  Global Arguments glue [G] D [i j] f x : rename.

  Axiom coh_cmp : forall (G:graph_composition) (D:diagram_composition G), forall x y z:G, forall Ɣ:G x y, forall δ:G y z, forall a:D x,
                  ap inc (cmp D Ɣ δ a) @ (glue D (graph2 δ Ɣ) a) = (glue D δ (diagram1 D Ɣ a)) @ (glue D Ɣ a).      

  Definition colimit_rect (G:graph_composition) (D: diagram_composition G) (P : colimit_composition D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@glue G D i j f x) # (q (diagram1 D f x)) = q x)
             (cmp_q : forall x y z:G, forall Ɣ:G x y, forall δ:G y z, forall a:D x,
  : forall w, P w
    := fun w => match w with colim i a => fun _ => q a end pp_q.

  Axiom colimit_rect_beta_pp
  : forall (G:graph) (D: diagram G) (P : colimit D -> Type)
           (q : forall i, forall x, P (colim x))
           (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q _ (diagram1 D f x)) = q _ x)
           (i j:G) (f: G i j) (x: D i),
      apD (@colimit_rect G D P q pp_q) (@pp G D i j f x) = pp_q i j f x.

  Definition colimit_rect_compute (G:graph) (D: diagram G) (P : colimit D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q (diagram1 D f x)) = q x) i (x:D i)
  : colimit_rect G D P (@q) pp_q (@colim _ _ i x) = q x.
    reflexivity.
  Defined.
  
End colimit_HIT.