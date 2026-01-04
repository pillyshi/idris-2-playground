-- Conjunction
data MyPair : Type -> Type -> Type where
     MyMkPair : {0 a, b : Type} -> (x : a) -> (y : b) -> MyPair a b

-- x : a
-- y : b
-- MyMkPair x y : MyPair a b (IC)

myFst : {0 a, b : Type} -> MyPair a b -> a
myFst (MyMkPair x y) = x

mySnd : {0 a, b : Type} -> MyPair a b -> b
mySnd (MyMkPair x y) = y

ttfp_exercise_45 : {0 a, b, c : Type} -> ((x : a) -> (y : b) -> c) -> (MyPair a b -> c)
ttfp_exercise_45 f x = f (myFst x) (mySnd x)

-- Implication
-- `->`そのものがImplicationなので少し対応がわかりにくい。

-- Disjunction
data MyEither : Type -> Type -> Type where
     Inl : {0 a, b : Type} -> {y : b} -> (x : a) -> MyEither a b
     Inr : {0 a, b : Type} -> {x : a} -> (y : b) -> MyEither a b
-- x : a
-- Inl x : MyEither a b (ID1)
-- y : b
-- Inr b : MyEither a b (ID2)

-- \bot
-- \top
-- Universal quantifier
-- Existencial quantifier

-- bool

-- N
-- bool is N_2

-- Natural number
