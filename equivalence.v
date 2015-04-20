Require Export Utf8_core.
Require Import HoTT.
Require Import lemmas .

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)


Section Things.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Definition S_le n : (n <= trunc_S n)%trunc.
  induction n. exact tt. exact IHn. Defined.

Definition Trunk (n:trunc_index) := {T:Type & IsTrunc n T}.

Definition HProp := Trunk -1.

Lemma IsEquiv_unique : forall (A B:Type), forall (h : A -> B), forall (f g : IsEquiv h), f=g.
Proof.
  intros.
  apply path_ishprop.
Defined.

Instance Contr_IsEquiv A B (f : A -> B) (a : IsEquiv f): IsTrunc minus_two (IsEquiv f).
apply BuildContr with (center := a).
intro; apply IsEquiv_unique.
Defined.

Lemma IsHProp_IsTrunc A : IsHProp A -> forall n:trunc_index, IsTrunc (trunc_S n) A.
  induction n. 
  - assumption. 
  - apply (@trunc_succ _ _ IHn).
Defined.

Definition equiv_is_mono_f (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : f x = f y -> x = y. 
  intro X. destruct H as [equiv_inv eisretr eissect eisadj].
  pose (Y := ap equiv_inv X).
  pose (eq1 := eissect x); pose (eq2 := eissect y).
  exact (eq1^ @ Y @ eq2).
Defined.

Instance equiv_is_mono_eq (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : IsEquiv (ap (x:=x) (y:=y) f).
apply (isequiv_adjointify _ (equiv_is_mono_f _ x y)).
- destruct H as [equiv_inv eisretr eissect eisadj].
  intro z. unfold equiv_is_mono_f.
  assert  (ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y) = (eisretr (f x))^ @ (eisretr (f x)) @ ap f (((eissect x)^ @ ap equiv_inv z) @ eissect y) @ (eisretr (f y))^ @ (eisretr (f y))) by hott_simpl.
  rewrite X. clear X.
  assert ((eisretr (f x)) @ ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y) @ (eisretr (f y)) ^
          =
          (ap f (ap equiv_inv ( ap f ((eissect x)^ @ (ap equiv_inv z) @ (eissect y)))))).

  apply concat_ap.
  exact eissect.

  rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^) (q := eisretr (f x)) (r := ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y)).
  rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^) (q := (eisretr (f x) @ ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y))) (r := (eisretr (f y)) ^).
  
  rewrite X. clear X.
  
  assert ((ap equiv_inv (ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y))) = ap equiv_inv z).
  rewrite concat_ap2 with (eissect := eissect).
  hott_simpl.
  exact eisretr.

  rewrite X. clear X.

  rewrite <- concat_ap with (eisretr := eisretr).

  hott_simpl.
  exact eissect.
- unfold equiv_is_mono_f.
  destruct H as [equiv_inv eisretr eissect eisadj]; intro z; destruct z.
  destruct (eissect x); reflexivity.
Defined.



Instance Tn_is_TSn : forall n, IsTrunc (trunc_S n) (Trunk n). (* Cf HoTT *)
intro n.
assert (Trunk n <~> TruncType n).
apply issig_trunctype.
refine (trunc_equiv _ _).
exact (TruncType n).
exact X^-1.
apply istrunc_trunctype.
apply isequiv_inverse.
Qed.


Definition HProp_contr A (B : A -> Type) (BProp : forall a, IsHProp (B a)) (a a' : A )
           (b : B a) (b' : B a') (e : a = a') : 
  Contr (e # b = b').
  destruct e.
  destruct (BProp a b b').
  apply BuildContr with (center := center).
  intro. apply (@path2_contr _ (contr_inhabited_hprop (B a) b) b b').
Defined.


Definition elim_E A B (f:A->B) (H:IsEquiv f) (x y : A) (p : f x = f y)
: x = y :=
  (eissect f x)^ @ @moveR_equiv_M _ _ (f ^-1) (isequiv_inverse _)_ _ p.


Definition True_is_irr (x y : Unit) : x = y.
  destruct x, y. reflexivity. Defined.

Instance true_ishprop : IsHProp Unit.
intros x y. apply BuildContr with (center := True_is_irr x y). 
intro e. destruct e, x. reflexivity.
Defined.

Definition HTrue := (Unit; true_ishprop) : HProp.


Lemma equal_equiv (A B:Type) (f g : A -> B) (eq_f : IsEquiv f) (eq_g : IsEquiv g)
: f = g -> (BuildEquiv _ _ f eq_f) = (BuildEquiv _ _ g eq_g).
  intro H. destruct H. assert (eq_f = eq_g).
  apply path_ishprop. destruct X. reflexivity.
Qed.

Lemma equal_inverse A (a b:A)
: (a=b) = (b=a).
  apply path_universe_uncurried.
  exists inverse.
  apply @isequiv_adjointify with (g := inverse);
    intro u; destruct u; reflexivity.
Defined.

Definition equiv_VV (A B:Type) (f:A -> B) (H:IsEquiv f)
: (f ^-1) ^-1 = f.
  hott_simpl.
Defined.

Definition moveR_EV (A B:Type) (f:A -> B) (IsEquiv:IsEquiv f) a b
: a = f b -> (f ^-1) a = b.
  intro p.
  apply moveR_equiv_M. rewrite equiv_VV. exact p.
Defined.


Lemma equal_equiv_inv (A B:Type) (f g: Equiv A B)
: f=g -> equiv_fun f = equiv_fun g.
  intro H. destruct H.
  reflexivity.
Qed.

Definition transport_path_universe_uncurried A B (f:A -> B) feq
: transport idmap (path_universe_uncurried (BuildEquiv _ _ f feq)) = f.
  assert (s := (eissect _ (IsEquiv := isequiv_path_universe (A:=A) (B:=B) ) (BuildEquiv _ _ f feq))).
  apply equal_equiv_inv in s.
  exact s.
Defined.

Lemma moveL_equiv_V  : forall (X Y:Type), forall (f: X -> Y), forall (H:IsEquiv f), forall (x:Y) (y:X), x = f y -> f^-1 x = y.
  intros X Y φ H u v HH.
  apply (@equiv_inj _ _ _ H).
  rewrite eisretr. exact HH.
Qed.

Lemma equiv_arrow (A B C:Type) (H : A <~> B)
: (A -> C) <~> (B -> C).
  refine (equiv_adjointify _ _ _ _).
  - intros f b; apply f. apply H; exact b.
  - intros f a; apply f. apply H; exact a.
  - intros f. apply path_forall; intro b. rewrite eisretr. reflexivity.
  - intros f. apply path_forall; intro a. rewrite eissect. reflexivity.
Defined.

Lemma moveR_EV2 (A C:Type) (B:A -> Type) (D:C -> Type) (f : (forall x, B x) -> (forall x, D x)) (H : IsEquiv f) (g:forall x, B x) (h:forall x, D x) (a:A)
: (f g = h) -> (f^-1 h a = g a).
  intro X. destruct X. rewrite eissect. reflexivity.
Qed.


End Things.