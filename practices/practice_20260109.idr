import Data.Fin

ttfp_exercise_415 : {0 a, b : Type} -- a = X, b = Y
  -> (p : a -> b -> Type)
  -> (y : b ** (x : a) -> p x y)
  -> ((x : a) -> (y : b ** p x y))
ttfp_exercise_415 p ((fst ** snd)) x = (fst ** snd x)

ttfp_exercise_416_1 : Either Bool Bool -> Bool
ttfp_exercise_416_1 (Left False) = False
ttfp_exercise_416_1 (Left True) = True
ttfp_exercise_416_1 (Right False) = False
ttfp_exercise_416_1 (Right True) = True

ttfp_exercise_416_2 : (x : Bool) -> (y : Bool) -> Bool
ttfp_exercise_416_2 False False = False
ttfp_exercise_416_2 False True = True
ttfp_exercise_416_2 True False = True
ttfp_exercise_416_2 True True = True

ttfp_exercise_416_3 : (x : Bool) -> (y : Bool) -> Bool
ttfp_exercise_416_3 False y = False
ttfp_exercise_416_3 True y = y

ttfp_exercise_417 : (x : Bool) -> (y : Bool) -> Bool
ttfp_exercise_417 False False = True
ttfp_exercise_417 False True = False
ttfp_exercise_417 True False = False
ttfp_exercise_417 True True = True

-- ttfp_exercise_418 : {n : Nat} -> (x : Fin n) -> (y : Fin n) -> Bool

