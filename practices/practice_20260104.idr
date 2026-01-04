ttfp_exercise_45 : {0 a, b, c : Type} -> (a -> b -> c) -> (Pair a b -> c)
ttfp_exercise_45 f x = f (fst x) (snd x)

ttfp_exercise_46 : {0 a, b, c : Type} -> (x : a) -> (y : Either b c) -> (Either (Pair a b) (Pair a c))
ttfp_exercise_46 x (Left y) = Left (x, y)
ttfp_exercise_46 x (Right y) = Right (x, y)

ttfp_exercise_47 : {0 a, b, c, d : Type} -> (f : a -> c) -> (g : b -> d) -> ((a, b) -> (c, d))
ttfp_exercise_47 f g (x, y) = (f x, g y)

ttfp_exercise_48_1 : {0 a : Type} -> a -> ((a -> Void) -> Void)
ttfp_exercise_48_1 x f = f x

ttfp_exercise_48_2 : {0 b, c : Type} -> Either b c -> ((b -> Void, c -> Void) -> Void)
ttfp_exercise_48_2 (Left x) y = fst y x
ttfp_exercise_48_2 (Right x) y = snd y x

ttfp_exercise_48_3 : {0 a, b, c : Type} -> (a -> b) -> ((a -> c) -> (a -> (b, c)))
ttfp_exercise_48_3 f g x = (f x, g x)

ttfp_exercise_49_1 : {0 a, b, c : Type} -> ((a, b) -> c) -> (a -> b -> c)
ttfp_exercise_49_1 f x y = f (x, y)

ttfp_exercise_49_2 : {0 a, b, c : Type} -> (a -> b -> c) -> ((a, b) -> c)
ttfp_exercise_49_2 f x = f (fst x) (snd x)



