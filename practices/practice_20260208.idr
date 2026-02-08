import Syntax.PreorderReasoning

infixl 8 `p`

-- Operators

0 Op1 : Type -> Type
Op1 a = a -> a

0 Op2 : Type -> Type
Op2 a = a -> a -> a

-- Laws

0 Associative : Op2 a -> Type
Associative p = {u, v, w : a} -> u `p` (v `p` w) === (u `p` v) `p` w

0 Commutative : Op2 a -> Type
Commutative p = {u, v : a} -> u `p` v === v `p` u

0 LeftNeutral : Op2 a -> (z : a) -> Type
LeftNeutral p z = {u : a} -> z `p` u === u

0 RightNeutral : Op2 a -> (z : a) -> Type
RightNeutral p z = {u : a} -> u `p` z === u

0 LeftInverse : Op2 a -> (z : a) -> (i : Op1 a) -> Type
LeftInverse p z i = {u : a} -> i u `p` u === z

0 RightInverse : Op2 a -> (z : a) -> (i : Op1 a) -> Type
RightInverse p z i = {u : a} -> u `p` i u === z

-- Lemmata

rightNeutral : LeftNeutral p z -> Commutative p -> RightNeutral p z
rightNeutral ln com = Calc $
  |~ u `p` z
  ~~ z `p` u ... com
  ~~ u ... ln

leftNeutral : RightNeutral p z -> Commutative p -> LeftNeutral p z
leftNeutral rn com = Calc $
  |~ z `p` u
  ~~ u `p` z ... com
  ~~ u ... rn

rightInverse : LeftInverse p z i -> Commutative p -> RightInverse p z i
rightInverse li com = Calc $
  |~ u `p` i u
  ~~ i u `p` u ... com
  ~~ z ... li

-- SemiGroup

-- Monoid

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
  -> u `p` v === z
  -> u === i v
solveInverseLeft g prf = Calc $
  |~ u
  ~~ u `p` z ..< g.rightNeutral
  ~~ u `p` (v `p` i v) ..< cong (u `p`) g.rightInverse
  ~~ (u `p` v) `p` i v ... g.associative
  ~~ z `p` i v ... cong (`p` i v) prf
  ~~ i v ... g.leftNeutral

-- 0 invertProduct
-- 0 rightInjective
-- 0 solveInverseRight
-- 0 inverseZero
-- 0 inverseInvolutory

-- record AbelianGroup
