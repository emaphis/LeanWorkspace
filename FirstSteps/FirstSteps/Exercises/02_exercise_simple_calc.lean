-- 02 - Simple Proof by Calculation and Substitution

import Mathlib.Tactic

-- prove that y = 0 where y = x^2 - 9 and x = -3 and x y are Reals

/-
Facts:
  x = x^2 - 9
  x = -3
Prove:
  y = 0

x, y, -3 and 9 are RealNumbers

Solution:
  y =  x^2 - 9    -- fact 1
    =  (-3)^2 - 9 -- fact 2 - substitution `rw`
    = 9 - 9       -- using arithmetic
    = 0           -- using arithmetic
-/

example {x y : ℝ} (h1 : y = x^2 - 9) (h2 : x = -3) : y = 0 :=
  calc
    y = x^2 - 9 := by rw [h1]
    _ = (-3)^2 - 9 := by rw [h2]
    _ = 9 - 9   := by norm_num
    _ = 0 := by norm_num
