Require Import MyTacs HoTT.
Require Import Peano nat_lemmas equivalence cech_nerve colimit colimit2.

Set Implicit Arguments.

Context `{fs : Funext}.
Context `{ua : Univalence}.


(* Squash *)
Notation sq A := (@tr -1 A).  

(* We want to prove that [Trunc -1 A] is the colimit of the Cech nerve of [sq: A -> Trunc -1 A]. *)

Section Prod_diagram.

  Definition kernel_pair_graph : graph.
    refine (Build_graph Bool _).
    intros X Y. exact (if X then if negb Y then Bool else False else False).
  Defined.
    
  Definition prod_diag (A:Type) : diagram kernel_pair_graph.
    refine (Build_diagram _ _ _).
    - simpl. intro i. exact (if i then A * A else A).
    - simpl. intros i j f. destruct i; simpl in *.
      destruct j; simpl in *. destruct f. exact (if f then snd else fst).
      destruct f.
  Defined.

End Prod_diagram.



Section TheProof.
  
  Variable (A:Type).
  Let D := prod_diag A.
  Variable Q : Type.
  Variable C : cocone D Q.
  Variable (colimQ : is_colimit C).
  
  Let pi := @snd Q A.

  Lemma isequiv_snd_QA
  : IsEquiv (pi : Q ∧ A -> A).
    refine (isequiv_adjointify _ _ _ _).
    - exact (λ x, (C.1 false x, x)).
    - intros x. reflexivity.
    - intros x. apply path_prod; [simpl|reflexivity].
      generalize x; apply ap10. clear x.
      specialize (colimit_product_r A colimQ); intros colimQA. unfold is_colimit in *.
      refine (equiv_inj (map_to_cocone (pdt_cocone_r A C) Q) _). 
      refine (path_cocone _ _).
      + intros i. simpl. set (H := C.2 true false); set (q := C.1) in *; simpl in q; simpl in H.
        destruct i.
        * intros [[x x'] y]. simpl.
          transitivity (q true (x, y)). exact (H true (x, y)). 
          transitivity (q false x). exact (H false (x, y))^.
          exact (H false (x, x')).
        * intros z. transitivity (q true z). exact (H true z).
          exact (H false z)^.
      + set (H0 := C.2 true false false) in *; set (H1 := C.2 true false true) in *; set (q0 := C.1 false) in *; set (q1 := C.1 true) in *.
        intros i j f. destruct i; destruct j; destruct f; simpl.
        * intros [[x x'] y]. simpl. fold H0 H1.
          match goal with
            |[|- ?CC1 @ (?CC2 @ (?CC3^ @ ?CC4)) = (?CC5 @ ?CC6^) @ ?CC7] => assert (CC1 = idpath)
          end.
          { etransitivity. unfold path_prod'.
          refine (ap_compose' _ _ _). etransitivity; [|apply ap_1]. apply ap.
          apply ap_snd_path_prod. }
          rewrite X; clear X. hott_simpl.
          match goal with
              |[|- _ = _ @ ?CC ] => assert (CC = H1 (x, x'))
          end. 
          apply ap_fst_path_prod. rewrite X; clear X.

          shelve.
        * intros [[x x'] y]. simpl. fold H0 H1.
          match goal with
            |[|- ?CC1 @ (?CC2 @ (?CC3^ @ ?CC4)) = (?CC5 @ ?CC6) @ ?CC7] => assert (CC1 = idpath)
          end. 
          { etransitivity. unfold path_prod'.
          refine (ap_compose' _ _ _). etransitivity; [|apply ap_1]. apply ap.
          apply ap_snd_path_prod. }
          rewrite X; clear X. hott_simpl.
          match goal with
            |[|- ?CC2 @ ?CC3^ @ ?CC4 = (?CC5 @ ?CC6) @ ?CC7] => assert (CC7 = CC4)
          end. 
          { apply ap_fst_path_prod. }
          rewrite X; clear X.
          reflexivity.
Admitted.

  
End TheProof.
