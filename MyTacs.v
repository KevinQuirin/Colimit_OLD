Require Import HoTT.

Ltac funext a := apply path_forall; intros a.

Ltac funext2 a b := funext a; funext b.

Ltac funext3 a b c := funext a; funext b; funext c.

Ltac funext4 a b c d := funext a; funext b; funext c; funext d.