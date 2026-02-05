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

0 LeftNeutral : (z : a) -> Op2 a -> Type
LeftNeutral z p = {u : a} -> z `p` u === u

0 RightNeutral : (z : a) -> Op2 a -> Type
RightNeutral z p = {u : a} -> u `p` z === u

0 LeftInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
LeftInverse z i p = {u : a} -> i u `p` u === z

0 RightInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
RightInverse z i p = {u : a} -> u `p` i u === z

-- Lemmata

rightNeutral : LeftNeutral z p -> Commutative p -> RightNeutral z p
rightNeutral ln com = Calc $
  |~ u `p` z
  ~~ z `p` u ... com
  ~~ u       ... ln

leftNeutral : RightNeutral z p -> Commutative p -> LeftNeutral z p
leftNeutral rn com = Calc $
  |~ z `p` u
  ~~ u `p` z ... com
  ~~ u       ... rn

--

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

record Monoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkMonoid
  associative : Associative p
  leftNeutral : LeftNeutral z p
  rightNeutral : RightNeutral z p

namespace Monoid
  (.sgrp) : Monoid a p z -> SemiGroup a p
  m.sgrp = MkSemiGroup m.associative

record CommutativeMonoid (a : Type) (p : Op2 a) (z : a) where
  constructor MkCommutativeMonoid
  associative : Associative p
  commutative : Commutative p
  leftNeutral : LeftNeutral z p
  -- rightNeutral can be derived from commutative and leftNeutral

mkCommutativeMonoid :
  {a : Type}
  -> {p : Op2 a}
  -> {z : a}
  -> ((u, v, w : a) -> (u `p` v) `p` w === u `p` (v `p` w))
  -> ((u, v : a) -> u `p` v === v `p` u)
  -> ((u : a) -> z `p` u === u)
  -> CommutativeMonoid a p z
mkCommutativeMonoid assoc comm ln =
  MkCommutativeMonoid (assoc _ _ _) (comm _ _) (ln _)

namespace CommutativeMonoid

  ||| A commutative monoid is also a semigroup
  (.sgrp) : CommutativeMonoid a p z -> SemiGroup a p 
  m.sgrp = MkSemiGroup m.associative

  ||| A commutative monoid is also a commutative semigroup
  (.csgrp) : CommutativeMonoid a p z -> CommutativeSemiGroup a p
  m.csgrp = MkCommutativeSemiGroup m.associative m.commutative
