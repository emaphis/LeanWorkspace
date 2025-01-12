-- 06 - Intermediate Results

import Mathlib.Tactic

-- Prove a = 2 given a = b+1 and a = 2 with a,b as Z integers

example {a b : ℤ} (h1 : a = b + 1) (h2 : b - 1 = 0) : a = 2 :=
  have h3: b = 1 := by linarith [h2]
  calc
    a = b + 1 := by rw [h1]
    _ = 1 + 1 := by rw [h3]
    _ = 2 := by norm_num
