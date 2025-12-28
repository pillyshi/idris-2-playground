import Data.Nat

proof1 : LTE 0 3
proof1 = LTEZero

proof2 : LTE 2 4
proof2 = LTESucc (LTESucc LTEZero)
