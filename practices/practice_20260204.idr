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
  ~~ u ... ln

leftNeutral : RightNeutral z p -> Commutative p -> LeftNeutral z p
leftNeutral rn com = Calc $
  |~ z `p` u
  ~~ u `p` z ... com
  ~~ u ... rn


