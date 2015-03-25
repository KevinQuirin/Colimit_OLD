Require Export Utf8_core.
Require Import HoTT.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

Section Univalence.
Context `{ua: Univalence}.
Context `{fs: Funext}.

Theorem log_equiv_is_equiv (A B:Type) {H : IsHProp A} {H' : IsHProp B} (f : A -> B) (g : B -> A) : 
  IsEquiv f.
  assert (Sect f g). intro x. apply path_ishprop; assumption.
  assert (Sect g f). intro x. apply path_ishprop; assumption.
  apply BuildIsEquiv with (eisretr := X0) (eissect := X).
  intro. destruct (H' (f (g (f x))) (f x)). rewrite <- contr. symmetry. apply contr.
Defined.

Theorem univalence_hprop (A B:Type) {H : IsHProp A} {H' : IsHProp B} : (A <-> B) -> A = B.
Proof.
  destruct 1 as [f g]. apply path_universe_uncurried.
  exists f. exact (log_equiv_is_equiv (H:=H) (H':=H') f g).
Defined.

Lemma eq_dep_subset' : forall A (B:A -> Type) (_:forall a, IsHProp (B a)) 
                             (a a':A) (H: B a) (H': B a'),
                        a = a' -> existT _ a H = existT _ a' H'.
  intros. apply (path_sigma' _ X0). destruct X0. apply (X a).
Defined.

Lemma eq_dep_subset : forall A (B:A -> Type) (_:forall a, IsHProp (B a)) 
                             (u v : sigT B),
                        u.1 = v.1 -> u = v.
  intros. apply (path_sigma _ _ _ X0). destruct u; destruct v; simpl in X0; destruct X0. apply path_ishprop. 
Defined.

Lemma isequiv_eq_dep_subset {A:Type} {B:A -> Type} (X : ∀ a : A, IsHProp (B a)) (u v : {a:A & B a})
: IsEquiv (eq_dep_subset X u v).
  apply @isequiv_adjointify with (g := λ p, ap pr1 p).
  - intro p. destruct p. simpl. unfold eq_dep_subset.
    destruct u as [a H]; simpl in *.
    assert (center (H=H) = idpath).
    apply contr.
    apply (transport (λ u, path_sigma B (a;H) (a;H) 1 u = idpath) X0^).
    reflexivity.
  - intro p.
    destruct u as [u G], v as [v H].
    simpl in p; destruct p. unfold eq_dep_subset.
    pose (foo := @ap_existT). unfold path_sigma' in foo.
    rewrite <- foo.
    simpl. unfold path_ishprop.
    destruct (center (G=H)). reflexivity.
Defined. 

End Univalence.