-- 1.1 Evaluating Expressions
-- Exercises

-- Find the values (evaluate).

#eval 42 + 19  -- 61

#eval String.append "A" (String.append "B" "C")
-- "ABC"

#eval String.append (String.append "A" "B") "C"
-- "ABC"

#eval if 3 == 3 then 5 else 7  -- 5

#eval if 3 == 4 then "equal" else "not equal"
-- "not equal"

-- Done

--  1.3 Functions and Definitions

-- 1.3.1.1.

def joinStringsWith (sep : String) (str1 : String) (str2 : String) :=
  String.append str1 (String.append sep str2)

#eval joinStringsWith ", " "one" "and another"
-- "one, and another"

#check joinStringsWith ": "  --  String → String

def volume (height : Nat) (width : Nat) (depth : Nat) :=
  height * width * depth
