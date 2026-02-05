ttfp_exercise_414 : {0 a : Type} -- a = X
  -> {0 b : a -> Type} -- A
  -> {0 c : a -> Type} -- B
  -> (p : (x : a) -> b x -> c x) -- (\forall x : X).(A \Rightarrow B)
  -> ((x : a ** b x) -> (x : a ** c x)) -- (\exists x : X).A \Rightarrow (\exists x : X).B
ttfp_exercise_414 p ((fst ** snd)) = (fst ** p fst snd)

