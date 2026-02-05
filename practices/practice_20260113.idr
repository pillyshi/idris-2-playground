import Data.Nat

infixl 8 `p`

0 Op1 : Type -> Type
Op1 a = a -> a

0 Op2 : Type -> Type
Op2 a = a -> a -> a

0 Associative : Op2 a -> Type
Associative p = {u, v, w : a} -> u `p` (v `p` w) === (u `p` v) `p` w

0 Commutative : Op2 a -> Type
Commutative p = {u, v : a} -> u `p` v === v `p` u

0 LeftNeutral : (z : a) -> Op2 a -> Type
LeftNeutral z p = {u : a} -> z `p` u === u

0 RightNeutral : (z : a) -> Op2 a -> Type
RightNeutral z f = {u : a} -> u `p` z === u 

0 LeftInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
LeftInverse z i p = {u : a} -> (i u) `p` u === z

0 RightInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
RightInverse z i f = {u : a} -> u `p` (i u) === z

record SemiGroup (a : Type) (p : Op2 a) where
  constructor MkSemiGroup
  associative : Associative p

record CommutativeSemiGroup (a : Type) (p : Op2 a) where
  constructor MkCommutativeSemiGroup
  associative : Associative p
  commutative : Commutative p

record Monoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkMonoid
  associative : Associative p
  leftNeutral : LeftNeutral z p
  rightNeutral : RightNeutral z p

record CommutativeMonoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkCommutativeMonoid
  associative : Associative p
  commutative : Commutative p
  leftNeutral : LeftNeutral z p
  rightNeutral : RightNeutral z p

record Group (a : Type) (p : Op2 a) (z : a) (i : Op1 a) where
  constructor MkGroup
  associative : Associative p
  leftNeutral : LeftNeutral z p
  rightNeutral : RightNeutral z p
  leftInverse : LeftInverse z i p
  rightInverse : RightInverse z i p

0 cmon_nat_plus : CommutativeMonoid Nat Z (+)
cmon_nat_plus =
  kCommutativeMonoid plusAssociative plusCommutative plusZeroLeftNeutral

