ttfp_exercise_413_1 : {0 a : Type} 
  -> {0 p : a -> Type}
  -> ((x : a) -> Not (p x)) -- (\forall x : a).(\neg p)
 -> Not (x : a ** p x) -- (\exists x : a).p
ttfp_exercise_413_1 f ((fst ** snd)) = f fst snd

ttfp_exercise_413_2 : {0 a : Type} 
  -> {0 p : a -> Type}
 -> Not (x : a ** p x) -- (\exists x : a).p
  -> ((x : a) -> Not (p x)) -- (\forall x : a).(\neg p)
ttfp_exercise_413_2 f x y = f (x ** y)


