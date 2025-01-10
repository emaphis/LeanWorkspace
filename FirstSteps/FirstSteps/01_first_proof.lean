-- 01 - First Simple Proof

import Mathlib.Tactic

-- Prove that a is greater than 1 where a = 4

example (a: ℕ) (h1 : a = 4) : a > 1 := by linarith

-- Or

example (a: ℕ) (h1 : a = 4) : a > 1 := by
  calc
    a = 4 := by rw [h1]
    _ > 1 := by norm_num
