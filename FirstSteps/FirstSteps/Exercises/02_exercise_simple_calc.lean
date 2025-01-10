-- 02 - Simple Proof by Calculation

import Mathlib.Tactic

-- prove that y = 0 where y = x^2 - 9 and x = -3 and x y are Reals

example {x y : ℝ} (h1 : y = x^2 - 9) (h2 : x = -3) : y = 0 :=
  calc
    y = x^2 - 9 := by rw [h1]
    _ = (-3)^2 - 9 := by rw [h2]
    _ = 0 := by norm_num
