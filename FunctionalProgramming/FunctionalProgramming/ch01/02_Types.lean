-- Types

-- declaring

#eval (1 - 2 : Nat)  --  0

#eval (1 - 2 : Int)  --  -1

--  checking the type
#check (1 - 2 : Int)  --  1 - 2 : Int

--  Impossible types

--#check String.append ["HELLO", " "] "world"
-- Can't append a list of Strings with a String
