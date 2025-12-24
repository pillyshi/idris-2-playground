plus_commutes_rhs_0 : (m : Nat) -> m = plus m 0
plus_commutes_rhs_0 0 = Refl
plus_commutes_rhs_0 (S k) = 
  let
    rec = plus_commutes_rhs_0 k
  in rewrite sym rec in Refl

plus_commutes_rhs_1 : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_rhs_1 k 0 = Refl
plus_commutes_rhs_1 k (S j) = rewrite plus_commutes_rhs_1 k j in Refl

total
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n -- what we want to prove. commutativity of plus function.
plus_commutes 0 m = plus_commutes_rhs_0 m
plus_commutes (S k) m = rewrite plus_commutes k m in plus_commutes_rhs_1 k m

plusReduceR_rhs_1 : (k : Nat) -> S (plus k 0) = S k
plusReduceR_rhs_1 0 = Refl
plusReduceR_rhs_1 (S k) = rewrite plusReduceR_rhs_1 k in Refl

total
plusReduceR : (n : Nat) -> plus n Z = n -- what we want to prove.
plusReduceR 0 = Refl
plusReduceR (S k) = plusReduceR_rhs_1 k

plus_assoc_rhs_1 : (k : Nat) -> (p : Nat) -> (m : Nat) -> S (plus k (plus m p)) = S (plus (plus k m) p)
plus_assoc_rhs_1 0 p m = Refl
plus_assoc_rhs_1 (S k) p m = rewrite plus_assoc_rhs_1 k p m in Refl

total
plus_assoc : (n, m, p : Nat) -> plus n (plus m p) = plus (plus n m) p
plus_assoc 0 m p = Refl
plus_assoc (S k) m p = plus_assoc_rhs_1 k p m

total
lemma_211 : (A : Type) -> (x, y : A) -> x = y -> y = x
lemma_211 a x y prf = sym prf

total
lemma_212 : (A : Type) -> (x, y, z : A) -> x = y -> y = z -> x = z
lemma_212 a x y z prf prf1 = trans prf prf1

lemma_214_1 : (A : Type) -> (x, y, z, w : A) -> (p : x = y) -> (q : y = z) -> (r : z = w) -> p = trans p (Refl {x = y})

