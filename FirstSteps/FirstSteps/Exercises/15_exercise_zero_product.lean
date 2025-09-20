-- 15 - Zero Product

import Mathlib.Tactic

-- Given p-1 ≠ 0 and q-2 ≠ 0
-- Prove (p-1)·(q-2) ≠ 0
-- Where p and q are rational numbers


example {p q : ℚ} (h: p - 1 ≠ 0 ∧ q - 2 ≠ 0) : (p - 1) * (q - 2) ≠ 0 := by
  apply mul_ne_zero_iff.mpr at h
  exact h
