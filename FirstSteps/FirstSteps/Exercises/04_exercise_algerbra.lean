-- 02 - Simple Algerbra

import Mathlib.Tactic

-- Prove y = a^2 - b^2 where y = (a-b)(a+b) and y, a, b are Reals

example {a b : ℝ} : (a - b) * (a + b)  = a^2 - b^2 :=
  calc
    (a - b) * (a + b) = a^2  - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring
