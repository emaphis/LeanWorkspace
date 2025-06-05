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
