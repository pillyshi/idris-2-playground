import Data.Nat

-- Introduction rule
data MyBool = MyFalse | MyTrue

not : (x : MyBool) -> MyBool
not MyFalse = MyTrue
not MyTrue = MyFalse

(&&) : (x : MyBool) -> (y : MyBool) -> MyBool
(&&) MyFalse y = MyFalse
(&&) MyTrue y = y

-- ttfp_exercise_416_1
(||) : (x : MyBool) -> (y : MyBool) -> MyBool
(||) MyFalse y = y
(||) MyTrue y = MyTrue

-- Elimination rule
ifThenElse : {0 a : Type} -> (x : MyBool) -> (l : a) -> (r : a) -> a
ifThenElse MyFalse l r = r
ifThenElse MyTrue l r = l

ttfp_exercise_421 : Nat -> Nat -> Bool
ttfp_exercise_421 0 0 = True
ttfp_exercise_421 0 (S k) = False
ttfp_exercise_421 (S k) 0 = False
ttfp_exercise_421 (S k) (S j) = ttfp_exercise_421 k j

