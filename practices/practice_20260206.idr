import Syntax.PreorderReasoning

infixl 8 `p`

-- Operators

0 Op1 : Type -> Type
Op1 a = a -> a

0 Op2 : Type -> Type
Op2 a = a -> a -> a

-- Laws

0 Associative : Op2 a -> Type
Associative p = {u, v, w : a} -> (u `p` v) `p` w === u `p` (v `p` w)

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


