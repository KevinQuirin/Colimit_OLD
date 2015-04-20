Require Import MyTacs HoTT.
Require Import equivalence lemmas nat_lemmas Peano colimit.

Context `{fs : Funext}.
Context `{ua : Univalence}.
  

Section hProduct.
  Definition a:nat := 12.
  Fixpoint hProduct (Y:Type) (n:nat) : Type :=
    match n with
      |0 => Unit
      |S m => Y /\ (hProduct Y m)
    end.

  Definition proj_hProduct (Y:Type) (n:nat) (P:hProduct Y n) : {p:nat & p < n} -> Y.
    induction n.
    - intros [p H]. apply not_lt_0 in H. destruct H.
    - intros [p H]. simpl in P.
      induction p.
      + exact (fst P).
      + apply le_pred in H. simpl in H.
        exact (IHn (snd P) (p;H)).
  Defined.

  Definition forget_hProduct (Y:Type) (n:nat) (P:hProduct Y (S n)) : {p:nat & p <= n} -> hProduct Y n.
    induction n.
    - intros [p H]. exact tt.
    - intros [p H]. simpl in P.
      induction p.
      + simpl. exact (fst (snd P), snd (snd P)).
      + apply le_pred in H. simpl in H.
        exact (fst P, (IHn (fst (snd P),snd (snd P)) (p;H))).
  Defined.
End hProduct.

Section hPullback.
  
  Definition char_hPullback {X Y:Type} (f:Y -> X) (n:nat) (P : hProduct Y (S n))
  : Type.
    induction n.
    - exact Unit. 
    - simpl in P.
      exact ((f (fst P) = f (fst (snd P))) /\ (IHn (snd P))).
  Defined.
  
  Definition char_hPullback_inv  {X Y:Type} (f:Y -> X) (n:nat) (P : hProduct Y (S n))
  : Type.
    induction n.
    - exact Unit. 
    - simpl in P.
      exact ((IHn (snd P)) /\ (f (fst P) = f (fst (snd P)))).
  Defined.
  
  Definition forget_char_hPullback {X Y:Type} (f:Y -> X) (n:nat)
             (x : hProduct Y (S (S n)))
             (P : (char_hPullback f (S n) x))
  : forall p:{p:nat & p <= n.+1}, (char_hPullback f n (forget_hProduct Y (S n) x p)).
    intros [p Hp].
    induction (decidable_paths_nat 0 p) as [| a].
    { destruct a0. simpl in *.
      exact (snd P). }
    
    induction (decidable_paths_nat (S n) p) as [| b].
    { destruct a0. simpl in *.
      induction n.
      simpl in *. exact tt.
      simpl in *.
      split. exact (fst P).
      apply IHn. exact (snd P).
      apply succ_not_0. }
    

    apply neq_symm in a.
    apply neq_0_succ in a.
    destruct a as [p' Hp'].
    (* destruct Hp'. *)
    assert (l := le_neq_lt _ _ (neq_symm _ _ b) Hp).
    assert (l0 := le_pred _ _ l). simpl in l0. clear b l. simpl in *. 
    generalize dependent n. generalize dependent p. generalize dependent p'. induction p'; intros.
    - simpl in *.
      destruct Hp'.   
      assert (k := gt_0_succ n l0); destruct k as [k Hk]. destruct Hk. simpl in *.
      split.
      exact (fst P @ (fst (snd P))).
      exact (snd (snd P)).
    - simpl in *.
      destruct Hp'.
      assert (n' := ge_succ_succ (S p') _ l0).
      destruct n' as [n' Hn']. destruct Hn'.  
      specialize (IHp' (p'.+1) idpath n' (snd x) (snd P)). simpl. split.
      exact (fst P).
      apply IHp'.
      exact (le_pred _ _ l0).
  Defined.

  (* Definition 7*)
  Definition hPullback {X Y:Type} (f:Y -> X) (n:nat)
  : Type.
    induction n.
    - exact Unit.
    - exact {P : hProduct Y (S n) & (char_hPullback f n P)}.
  Defined.

  Definition proj_pullback {X Y:Type} (f:Y -> X) (n:nat) (P : hPullback f n) : forall p:{p:nat & p < n}, Y.
    apply proj_hProduct.
    induction n. exact P. simpl in *. exact P.1.
  Defined.

  (* This defines the canonical projections between the n+1-pullback of X to the n-pullback of X*)
  Definition forget_hPullback {X Y:Type} (f:Y -> X) (n:nat) (P : hPullback f (S n)) : forall p:{p:nat & p <= n}, hPullback f n.
    intros [p Hp].
    induction n. exact tt.
    exists (forget_hProduct Y (S n) P.1 (p;Hp)).
    apply forget_char_hPullback.
    exact P.2.
  Defined.

End hPullback.


Section Cech_Nerve.
  
  (* Definition 8*)
  Definition Cech_nerve_graph : graph.
    refine (Build_graph _ _).
    exact nat.
    intros m n.
    exact ((S n = m) /\ (nat_interval m)).
  Defined.

  Definition Cech_nerve_diagram {X Y:Type} (f: Y -> X) : diagram (Cech_nerve_graph).
    refine (Build_diagram _ _ _).
    intro n.
    exact (hPullback f (S n)).
    intros i j. 
    intros [p q] a.
    destruct p.
    apply forget_hPullback.
    exact a.
    exact q.
  Defined.

  Definition Cech_nerve_commute {X Y:Type} (f: Y -> X)  
  : forall i, (Cech_nerve_diagram f) i -> X.
    intro i. simpl. intro P.
    exact (f (fst P.1)).
  Defined.

  Definition Cech_nerve_pp {X Y:Type} (f: Y -> X)
  : forall i j, forall (g : Cech_nerve_graph i j), forall (x : (Cech_nerve_diagram f) i),
      (Cech_nerve_commute f) _ (diagram1 (Cech_nerve_diagram f) g x) = (Cech_nerve_commute f ) _ x.
    intros i j g x. simpl in *.
    unfold Cech_nerve_commute. simpl.
    destruct g as [p [q Hq]]. destruct p. simpl.
    destruct q; [exact (fst (x.2))^ | reflexivity].
  Defined.

  
End Cech_Nerve.
