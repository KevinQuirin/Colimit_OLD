Require Export Utf8_core.
Require Import HoTT.
Require Import equivalence lemmas colimit.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.

Section Pushout.
  
  Context `{fs : Funext}.

  Inductive Pushout_graph_shape :=
    |Pushout_Corner : Pushout_graph_shape
    |Pushout_Left : Pushout_graph_shape
    |Pushout_Down : Pushout_graph_shape.
 
  
  Definition pushout_graph : graph.
    refine (Build_graph _ _).
    - exact Pushout_graph_shape.
    - intros A B. induction A.
      induction B.
      exact Empty.
      exact Unit.
      exact Unit.
      exact Empty.
      exact Empty.
  Defined.

  Definition pushout_diag {A B C:Type} (f:A -> B) (g:A -> C) : diagram pushout_graph.
    refine (Build_diagram _ _ _).
    - intro x; induction x.
      exact A. exact B. exact C.
    - intros i j; induction i, j; try (intro H; destruct H); simpl.
      exact f. exact g.
  Defined.

End Pushout.

Section Coequalizers.

  Inductive coeq_graph_shape :=
|Coeq_Left : coeq_graph_shape
|Coeq_Right : coeq_graph_shape.

  Definition coeq_graph : graph.
    refine (Build_graph _ _).
    - exact coeq_graph_shape.
    - intros i j. induction i.
      induction j. exact Empty. exact Bool. exact Empty.
  Defined.

  Definition coeq_diagram {A B:Type} (f g:A -> B) : diagram coeq_graph.
    refine (Build_diagram _ _ _).
    - intro i; induction i. exact A. exact B.
    - intros i j; induction i, j; try (intro H; destruct H); simpl.
      exact f. exact g.
  Defined.
  
End Coequalizers.