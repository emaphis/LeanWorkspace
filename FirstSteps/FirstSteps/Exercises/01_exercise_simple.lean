-- 01 - First Proof

import Mathlib.Tactic

-- Prove  a < 10 given a = 3. a is a Natural number

example (a : ℕ) (h1 : a = 4) : a < 10 := by
  calc
    a = 4  := by rw [h1]
    _ < 10 := by norm_num
