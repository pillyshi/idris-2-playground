-- x : a
-- y : a
-- x =_a y => p(x) => p(y)
-- ReflはEqual x x型の値
-- substitution Refl : p x -> p y
substitution : {0 a : Type} -> {0 p : a -> Type} -> {x, y : a} -> x = y -> p x -> p y
substitution Refl px = px

-- x : a
-- y : a
-- x =_a y => y =_a x
symmetry : {0 a : Type} -> {x, y : a} -> x = y -> y = x
symmetry {x} {y} prf = 
  let 
    p : a -> Type
    p = \z => z = x

    px : p x
    px = Refl

    py : p y
    py = substitution {p = p} prf px
  in py

-- x : a
-- y : a
-- z : a
-- x =_a y => y =_a z => x =_a z
transitivity : {0 a : Type} -> {x, y, z : a} -> x = y -> y = z -> x = z
transitivity {x} {y} {z} p1 p2 =
  let
    p : a -> Type
    p = \u => u = z
    px : p x
    px = substitution {p = p} (symmetry p1) p2
  in px
