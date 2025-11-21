-- 1.1 Evaluating expressions

-- Mathematice expressons

#eval 3 + 4

#eval 3 * 4

#eval 1 + 2 * 5 -- order of operations

-- Strings

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "It is " (if 1 > 2 then "yes" else "no")


-- Messages You May Meet - Errors

--#eval String.append "It is "

-- could not synthesize a 'Repr' or 'ToString' instance for type
--  String → String

-- Done
