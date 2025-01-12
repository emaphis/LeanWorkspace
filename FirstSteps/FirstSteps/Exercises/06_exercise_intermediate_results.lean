-- 06 - Intermediate Results Exercise

import Mathlib.Tactic

-- Prove a = 2 given a = b + c and b - 1 = 0 and c + 1 = 2
--   with a,b,c as Z integers

example {a b c : ℤ} (h1 : a = b + c) (h2 : b - 1 = 0) (h3 : c + 1 = 2) : a = 2 :=
  have h4: b = 1 := by linarith [h2]
  have h5: c = 1 := by linarith [h3]
  calc
    a = b + c := by rw [h1]
    _ = 1 + 1 := by rw [h4, h5]
    _ = 2 := by norm_num
