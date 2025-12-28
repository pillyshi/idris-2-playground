import Data.Nat

-- myLteSuccRight : LTE n m -> LTE n (S m)
-- myLteSuccRight LTEZero = LTEZero
-- myLteSuccRight (LTESucc x) = LTESucc (myLteSuccRight x)
-- C-c C-s, C-c C-C, C-c C-aを使うだけで簡単に証明できてしまう。すごい。しかし、意味を理解したい。

-- myLteSuccRight : LTE n m -> LTE n (S m)
-- myLteSuccRight LTEZero = ?myLteSuccRight_rhs_0
-- myLteSuccRight (LTESucc x) = ?myLteSuccRight_rhs_1

--  0 m : Nat
--  0 n : Nat
--    x : LTE n m
--    x = LTEZero or LTESucc x
--    myLteSuccRight LTEZero : LTE 0 m
--    myLteSuccRight LTEZero = LTEZero : LTE 0 m
--    LTEZero : LTE 0 m
--    LTESucc x : LTE (S n) (S m)
--    myLteSuccRight x : LTE n (S m)
--    myLteSuccRight (LTESucc x) : LTE (S n) (S (S m))
--    myLteSuccRight (LTESucc x) = LTESucc (myLteSuccRight x) : LTE (S n) (S (S m))
-- ------------------------------
-- myLteSuccRight_rhs : LTE n (S m)

-- Data.Nat.LTEZero : LTE 0 right
-- Data.Nat.LTESucc : LTE left right -> LTE (S left) (S right)

-- myLteSuccRight LTEZero : LTE 0 (S right)
-- (LTESucc x) : LTE (S n) (S m)

--  0 m : Nat
--  0 n : Nat
-- ------------------------------
-- myLteSuccRight_rhs_0 : LTE 0 (S m)
  
