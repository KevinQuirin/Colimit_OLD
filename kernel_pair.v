Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.
Require Import equivalence lemmas colimit cech_nerve.


Section Kernel_pair.

  Definition kernel_pair_graph : graph
    := Build_graph Bool (λ u v, (match u,v with
                                   |true, true => Empty
                                   |true, false => Bool
                                   | _,_ => Empty
                                 end)).

  Definition kernel_pair {A B:Type} (f : A -> B) : diagram kernel_pair_graph.
    refine (Build_diagram _ _ _).
    - intros u.
      exact (match u with
               |true => Pullback f f
               |false => A
             end).
    - intros i j h. simpl.
      destruct i,j. simpl in *. destruct h.
      simpl in *.
      exact (if h then pullback_pr1 else pullback_pr2).
      simpl in h. destruct h.
      simpl in h. destruct h.
  Defined.

  Definition kernel_pair_commute {A B: hSet} (f : A -> B)
  : ∀ i : kernel_pair_graph, kernel_pair f i → B.
    intros i. simpl in *.
    destruct i.
    exact (f o (pullback_pr1)).
    exact f.
  Defined.

  Definition kernel_pair_pp {A B: hSet} (f : A -> B)
  : ∀ (i j : kernel_pair_graph) (h : kernel_pair_graph i j) (x : kernel_pair f i), kernel_pair_commute f j (diagram1 (kernel_pair f) h x) = kernel_pair_commute f i x.
    intros i j h x.
    simpl in *.
    destruct i, j; simpl in *; destruct h.
    reflexivity.
    exact x.2.2^.
  Defined.
        
End Kernel_pair.

Section Foo.

  Context `{ua : Univalence}.
  Context `{fs : Funext}.

  
      
  
End Foo.