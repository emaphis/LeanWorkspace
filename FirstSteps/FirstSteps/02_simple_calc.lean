-- 02 - Simple Proof by Calculation

import Mathlib.Tactic

-- prove that y = 7 where y = x + 4 and x = 3 and x u are Reals

example {x y : ℝ} (h1 : y = x + 4) (h2 : x = 3) : y = 7 :=
  calc
    y = x + 4 := by rw [h1]
    _ = 3 + 4 := by rw [h2]
    _ = 7 := by norm_num
