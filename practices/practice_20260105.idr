ttfp_exercise_412 : {0 a : Type} 
  -> {0 p : a -> Type} 
  -> (x : a ** Not (p x)) 
  -> Not ((x : a) -> p x)
ttfp_exercise_412 ((fst ** snd)) f = snd (f fst)

