substitution : {0 a : Type} -> {0 p : a -> Type} -> {x, y : a} -> x = y -> p x -> p y
substitution Refl px = px

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

transitivity : {0 a : Type} -> {x, y, z : a} -> x = y -> y = z -> x = z
transitivity {x} {y} {z} p1 p2 =
  let
    p : a -> Type
    p = \u => u = z
    px : p x
    px = substitution {p = p} (symmetry p1) p2
  in px
