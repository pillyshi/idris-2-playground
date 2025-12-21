substEq : {0 a : Type} -> {0 p : a -> Type} -> {x, y : a} -> x = y -> p x -> p y
substEq Refl px = px
