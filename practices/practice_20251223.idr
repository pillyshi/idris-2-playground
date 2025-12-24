-- Is (Nat, plus) group?
my_apply :
  {A : Type}
  -> (a : A)
  -> (f : A -> A)
  -> A
my_apply a f = f a

well_defined :
  (A : Type)
  -> (f : A -> A -> A)
  -> {x1, y1, x2, y2 : A}
  -> x1 = x2
  -> y1 = y2
  -> f x1 y1 = f x2 y2

--- 型 (type) を定義して値 (judgment) を見つける。

-- f : Equal 1 1 -- Equal 1 1型のjudgment
-- f = Refl -- proof

-- g : Equal 1 2 -- Equal 1 2型のjudgment
-- g = Refl -- proof but raise Error. 

-- 変数のスコープを制御したいな。
-- Integerはprimitive type。Natはdata type。
-- (Integer, plus)は群になる。こういうのを示したい。
-- Integerをdata typeで表現しないといけない気がするが。

-- Reflがわからない。単純だが難しすぎる。
-- Equalを理解しないと。
-- Equalはdata type。
-- EqualはTypeを返す関数。
-- Equalは述語。Equal a bは命題（型）。

plus_commutes_rhs_0_rhs_1 : (k : Nat) -> S k = S (plus k 0)

plus_commutes_rhs_0 : (m : Nat) -> m = plus m 0
plus_commutes_rhs_0 0 = Refl
plus_commutes_rhs_0 (S k) = plus_commutes_rhs_0_rhs_1 k

-- https://idris2.readthedocs.io/en/latest/proofs/patterns.html
-- plusのcommutativityを証明する試み
-- emacsの拡張機能が優秀らしいので久しぶりにemacsを使っている。
-- まず、型を定義する
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
-- Pressing C-c C-s yields:
plus_commutes Z m = plus_commutes_rhs_0 m
plus_commutes (S k) m = ?plus_commutes_rhs_1

