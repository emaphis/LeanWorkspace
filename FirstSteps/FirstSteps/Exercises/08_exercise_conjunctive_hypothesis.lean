-- 08 - Conjunctive "and" Hypothesis

import Mathlib.Tactic

-- Write a Lean program to show that y≥8, given (x ≥ 5) ∧ (y = x+3), where x,y ∈ ℤ.

example {x y : ℤ} (h : x ≥ 5 ∧ y = x + 3) : y ≥ 8 := by
  obtain ⟨ ha , hb ⟩ := h
  calc
    y = x + 3 := by rw [hb]
    _ ≥ (5) + 3 := by rel [ha]
    _ = 8 := by norm_num
