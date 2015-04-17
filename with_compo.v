Require Import Utf8_core.
Require Import HoTT.
Require Import equivalence cech_nerve colimit colimit2.
Require Import Peano nat_lemmas.

Context `{fs : Funext}.
Context `{ua : Univalence}.

Section Graph_with_composition.

  Record graph_composition :=
    { graph0 :> Type;
      graph1 :> graph0 -> graph0 -> Type;
      graph2 : forall x y z:graph0, (graph1 y z) -> (graph1 x y) -> (graph1 x z) }.
  
  Global Arguments graph2 [G] {x y z} Ɣ δ : rename.

  Record diagram_composition (G : graph_composition) :=
    { diagram0 :> G -> Type;
      diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j);
      cmp : forall x y z:G, forall Ɣ:G x y, forall δ:G y z,
              (diagram1 y z δ) o (diagram1 x y Ɣ) == (diagram1 x z (graph2 δ Ɣ)) }.
  
  Global Arguments diagram0 [G] D i : rename.
  Global Arguments diagram1 [G] D [i j] f x : rename.
  Global Arguments cmp [G] D [x y z] Ɣ δ t: rename.

End Graph_with_composition.

Section Cocone_composition.

  Record cocone_composition {G:graph_composition} (D:diagram_composition G) (T:Type) :=
    {cocone_q : forall i, D i -> T;
     cocone_p : forall (i j:G) (f: G i j) (x: D i), cocone_q j (diagram1 D f x) = cocone_q i x;
     cocone_pp : forall (i j k:G) (f: G j k) (g: G i j) (x:D i),
                   (cocone_p j k f (diagram1 D g x)) @ (cocone_p i j g x) = (ap (cocone_q k) (cmp D g f x)) @ (cocone_p i k (graph2 f g) x)}.

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

Section Kernel_pair.
  
  Definition KP_graph : graph_composition.
    refine (Build_graph_composition _ _ _).
    - exact Bool.
    - intros i j.
      exact (match i, j with
        |true, false => Bool
        |true, true => Bool + Unit
        |false, false => Unit
        |false, true => Unit
             end).
    - intros i j k f g.
      simpl in *.
      destruct i.
      (* i= true *)
      destruct j.
      (* j=true *)
      destruct k.
      (* k = true *)
      destruct f, g.
      destruct b.
      exact g.
      (* k=false *)
      


  
End Kernel_pair.


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