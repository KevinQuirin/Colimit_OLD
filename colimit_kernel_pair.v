2 focused subgoals
(unfocused: 1-0-0), subgoal 1 (ID 1910)
  
  A : Type
  D := prod_diag A : diagram Cech_nerve_graph
  Q : Type
  C : cocone D Q
  colimQ : ∀ X : Type, IsEquiv (map_to_cocone C X)
  pi := snd : Q ∧ A → A
  x : Q ∧ A
  colimQA : ∀ X : Type, IsEquiv (map_to_cocone (pdt_cocone_r A C) X)
  u1, u2, v : A
  p := C.2 1 0 (1, (1; le_n 1)) (v, (u1, tt))
    : C.1 0 (v, tt) = C.1 1 (v, (u1, tt))
  p0 := (C.2 1 0 (1, (0; le_0 1)) (v, (u1, tt)))^
     : C.1 1 (v, (u1, tt)) = C.1 0 (u1, tt)
  ============================
   C.2 1 0 (1, (1; le_n 1)) (v, (u1, tt)) @
   (C.2 1 0 (1, (0; le_0 1)) (v, (u1, tt)))^ =
   (C.2 1 0 (1, (1; le_n 1)) (v, (u2, tt)) @
    (C.2 1 0 (1, (0; le_0 1)) (v, (u2, tt)))^) @
   (C.2 1 0 (1, (0; le_0 1)) (u1, (u2, tt)) @
    (C.2 1 0 (1, (1; le_1_Sn 0)) (u1, (u2, tt)))^)

subgoal 2 (ID 1426) is:
 (C.2 1 0 (1, (1; le_n 1)) (v, (u1, tt)) @
  (C.2 1 0 (1, (0; le_0 1)) (v, (u1, tt)))^) @
 (ap ((let (proj1_sig, _) := C in proj1_sig) 0)
    (path_prod (u1, tt) (u1, tt) 1 (path_ishprop tt tt)) @
  C.2 1 0 (1, (1; le_1_Sn 0)) (u1, (u2, tt))) =
 match
   (let
    (_, snd) :=
    nat_rect (λ p0 : nat, p0 <= 1 → A ∧ Unit) (λ _ : 0 <= 1, (u2, tt))
      (λ (p0 : nat) (_ : p0 <= 1 → A ∧ Unit) (_ : p0.+1 <= 1), (u1, tt)) q Hq
    in
    snd) as u
   return
     (C.1 0 (v, tt) =
      C.1 0
        (let
         (fst, _) :=
         nat_rect (λ p0 : nat, p0 <= 1 → A ∧ Unit) 
           (λ _ : 0 <= 1, (u2, tt))
           (λ (p0 : nat) (_ : p0 <= 1 → A ∧ Unit) (_ : p0.+1 <= 1), (u1, tt))
           q Hq in
         fst, u))
 with
 | tt =>
     C.2 1 0 (1, (1; le_n 1))
       (v,
       (let
        (fst, _) :=
        nat_rect (λ p0 : nat, p0 <= 1 → A ∧ Unit) (λ _ : 0 <= 1, (u2, tt))
          (λ (p0 : nat) (_ : p0 <= 1 → A ∧ Unit) (_ : p0.+1 <= 1), (u1, tt))
          q Hq in
        fst, tt)) @
     (C.2 1 0 (1, (0; le_0 1))
        (v,
        (let
         (fst, _) :=
         nat_rect (λ p0 : nat, p0 <= 1 → A ∧ Unit) 
           (λ _ : 0 <= 1, (u2, tt))
           (λ (p0 : nat) (_ : p0 <= 1 → A ∧ Unit) (_ : p0.+1 <= 1), (u1, tt))
           q Hq in
         fst, tt)))^
 end @ C.2 1 0 (1, (q; Hq)) (u1, (u2, tt))