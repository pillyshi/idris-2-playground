-- Conjunction (\wedge)
-- Formation rule for \wedge
-- a is a type \equiv_{df} a : Type
-- b is a type \equiv_{df} b : Type
-- a \wedge b is a type : a \wedge b : Type

-- Introduction rule for \wedge
-- x : a
-- y : b
-- (x, y) : a \wedge b

-- Elimination rule for \wedge
-- r : a \wedge b
-- fst r : a
-- snd r : b

-- Computation rule for \wedge
-- fst (x, y) \to x
-- snd (x, y) \to y

data MyPair : Type -> Type -> Type where
  MyMkPair : {0 a, b : Type} -> (x : a) -> (y : b) -> MyPair a b -- I \wedge

-- x : a
-- y : b
-- MyMkPair x y : MyPair a b

myFst : {0 a, b : Type} -> MyPair a b -> a -- E \wedge_1
myFst (MyMkPair x y) = x -- C \wedge_1

mySnd : {0 a, b : Type} -> MyPair a b -> b -- E \wedge_2
mySnd (MyMkPair x y) = y -- C \wedge_2

-- Implication (\Rightarrow)
-- a : Type
-- b : Type
-- a -> b : Type

-- Introduction rule for \Rightarrow

-- Elimination rule for \Rightarrow
-- x : a
-- f : a -> b
-- f x : b

-- Computation rule for \Rightarrow

-- Disjunction (\vee)
-- Formation rule for \vee
-- a : Type
-- b : Type
-- a \vee b : Type

-- Introduction rule for \vee
-- x : a
-- y : b
-- inl x : a \vee b
-- inr y : a \vee b

-- Elimination rule for \vee
-- p : a \vee b
-- f : a -> c
-- g : b -> c
-- cases p f g : c

-- Computation rule for \vee
-- cases (inl x) f g \to f x
-- cases (inr y) f g \to g y

data MyEither : (a : Type) -> (b : Type) -> Type where
  MyLeft : (x : a) -> MyEither a b
  MyRight : (x : b) -> MyEither a b

