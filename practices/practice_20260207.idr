import Syntax.PreorderReasoning

infixl 8 `p`

-- Operator

0 Op1 : Type -> Type
Op1 a = a -> a

0 Op2 : Type -> Type
Op2 a = a -> a -> a

-- Laws

0 Associative : Op2 a -> Type
Associative p = {u, v, w : a} -> u `p` (v `p` w) === (u `p` v) `p` w

0 Commutative : Op2 a -> Type
Commutative p = {u, v : a} -> p u v === p v u

0 LeftNeutral : Op2 a -> (z : a) -> Type
LeftNeutral p z = {u : a} -> p z u === u

0 RightNeutral : Op2 a -> (z : a) -> Type
RightNeutral p z = {u : a} -> p u z === u

0 LeftInverse : Op2 a -> (z : a) -> (i : Op1 a) -> Type
LeftInverse p z i = {u : a} -> p (i u) u === z

0 RightInverse : Op2 a -> (z : a) -> (i : Op1 a) -> Type
RightInverse p z i = {u : a} -> p u (i u) === z

-- Lemmata
0 leftNeutral : RightNeutral p z -> Commutative p -> LeftNeutral p z
leftNeutral rn com = Calc $
  |~ p z u
  ~~ p u z ... com
  ~~ u ... rn  

0 rightNeutral : LeftNeutral p z -> Commutative p -> RightNeutral p z
rightNeutral ln com = Calc $
  |~ p u z
  ~~ p z u ... com
  ~~ u ... ln

-- SemiGroup

record SemiGroup (a : Type) (p : Op2 a) where
  constructor MkSemiGroup
  associative : Associative p

record CommutativeSemiGroup (a : Type) (p : Op2 a) where
  constructor MkCommutativeSemiGroup
  associative : Associative p
  commutative : Commutative p

namespace CommutativeSemiGroup

  (.sgrp) : CommutativeSemiGroup a p -> SemiGroup a p
  c.sgrp = MkSemiGroup c.associative

-- Monoid

record Monoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkMonoid
  associative : Associative p
  leftNeutral : LeftNeutral p z
  rightNeutral : RightNeutral p z

namespace Monoid
  (.sgrp) : Monoid a p z -> SemiGroup a p
  m.sgrp = MkSemiGroup m.associative

record CommutativeMonoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkCommutativeMonoid
  associative : Associative p
  commutative : Commutative p
  leftNeutral : LeftNeutral p z
  -- rightNeutral can be derive from leftNeutral and commutative

namespace CommutativeMonoid

  (.csgrp) : CommutativeMonoid a p z -> CommutativeSemiGroup a p
  m.csgrp = MkCommutativeSemiGroup m.associative m.commutative

-- Group

record Group (a : Type) (p : Op2 a) (z : a) (i : Op1 a) where
  constructor MkGroup
  associative : Associative p
  leftNeutral : LeftNeutral p z
  rightNeutral : RightNeutral p z
  leftInverse : LeftInverse p z i
  rightInverse : RightInverse p z i


0 leftInjective : Group a p z i
  -> {u, v, w : a}
  -> u `p` v === u `p` w
  -> v === w
leftInjective g prf = Calc $
  |~ v
  ~~ z `p` v ..< g.leftNeutral
  ~~ (i u `p` u) `p` v ..< cong (`p` v) g.leftInverse
  ~~ i u `p` (u `p` v) ..< g.associative
  ~~ i u `p` (u `p` w) ... cong (i u `p`) prf
  ~~ (i u `p` u) `p` w ... g.associative
  ~~ z `p` w ... cong (`p` w) g.leftInverse
  ~~ w ... g.leftNeutral

0 solveInverseLeft : Group a p z i
  -> {u, v : a}
  -> v `p` u === z
  -> u === i v
solveInverseLeft g prf = Calc $
  |~ u
  ~~ z `p` u ..< g.leftNeutral
  ~~ (i v `p` v) `p` u ..< cong (`p` u) g.leftInverse
  ~~ i v `p` (v `p` u) ..< g.associative
  ~~ i v `p` z ... cong (i v `p`) prf
  ~~ i v ... g.rightNeutral

0 invertProduct
