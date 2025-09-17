-- 02 - Simple Proof by Calculation and Substitution

import Mathlib.Tactic

-- prove that y = 7 where y = x + 4 and x = 3 and x u are Reals

/-
Facts:
  y = x + 7
  x = 3

Prove:
  y = 7

Given: x, y are Reals

Solution:
  y = x + 4    given fact (1)
    = (3) + 4  given fact (2)
    = 7        normal math
-/

example {x y : ℝ} (h1 : y = x + 4) (h2 : x = 3) : y = 7 :=
  calc
    y = x + 4 := by rw [h1]
    _ = 3 + 4 := by rw [h2]
    _ = 7 := by norm_num

/-
Facts:
  x = x^2 - 9
  x = -3
Prove:
  y = 0

x, y, -3 and 9 are RealNumbers

Solution:
  y =  x^2 - 9    -- fact 1
    =  (-3)^2 - 9 -- fact 2 - substitution
    = 9 - 9       -- using normal arithmetic
    = 0           -- using normal arithmetic
-/

example {x y : ℝ} (h1 : y = x^2 - 9) (h2 : x = -3) : y = 0 := by
  calc
    y = x^2 - 9 := by rw [h1]
    _ = (-3)^2 - 9 := by rw [h2]
    _ = 9 - 9 := by norm_num
    _ = 0  := by norm_num
