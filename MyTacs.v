Require Export Utf8_core.
Require Import HoTT.

Ltac funext a := apply path_forall; intros a.

Ltac funext2 a b := funext a; funext b.

Ltac funext3 a b c := funext a; funext b; funext c.

Ltac funext4 a b c d := funext a; funext b; funext c; funext d.

Ltac funext5 a b c d e := funext a; funext b; funext c; funext d; funext 5.

(* Applies path_forall as many times as possible. Usage : funext'; intros a b c d ... *)
Ltac funext' :=
  match goal with
    |[|- ?f = ?g] =>
     match type of f with
       |forall x:_, _ => let x := fresh x in
                         apply path_forall; intro x; funext'; revert x
     end
    |_ => idtac
    end.
