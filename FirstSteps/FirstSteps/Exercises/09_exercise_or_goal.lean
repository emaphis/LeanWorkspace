-- 09 - "Or" Goal

import Mathlib.Tactic

/-
For integer x = -1 show that
  (x = 1) ∨ (x^2 = 1) ∨ (x^3 = 1)

 x^3 = 1 ??

Solve:
  x = -1                  given fact
  (x^2 = 1) ∨ (x^3 = 1)   objective

  x^2 = 1                 sufficienct goal (2)

  x^2 = (-1)^2    using fact (1)
      = 1         using arithmetic
-/

example {x : ℤ} (h : x = -1) : x = 1 ∨ x^2 = 1 ∨ x^3 = 1 := by
  right
  left
  calc
    x^2 = (-1)^2  := by rw [h]
    _   = 1   := by norm_num

-- `left` select left part of goal, `right` selects the rest of the goal
