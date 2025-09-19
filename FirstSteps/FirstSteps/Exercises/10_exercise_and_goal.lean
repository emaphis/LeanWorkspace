-- 10 - "And" Goal - conjunction

import Mathlib.Tactic

-- For integer x, given that x = -1, show that
--      (x^3 = -1) ∧ (x^4 = 1) ∧ (^5 = -1)

/-
  x = -1                    given fact
  (x^3 = -1) ∧ (x^4 = 1) ∧ (^5 = -1)    proof objective

    x^3 = (-1)^3              using fact (1)
        = - 1                 using arithmetic

    x^4 = (-1)^4              using fact (1)
        = 1                   using arithmetic

    x^5 = (-1)^5              using fact (1)
        = - 1                 using arithmetic
-/

example {x : ℤ} (h: x = -1) : x^3 = -1 ∧ x^4 = 1 ∧ x^5 = -1 := by
  constructor
  · calc
      x^3 = (-1)^3  := by rw[h]
      _   = -1      := by norm_num
  constructor
  · calc
      x^4 = (-1)^4  := by rw[h]
      _   = 1      := by norm_num
  · calc
      x^5 = (-1)^5  := by rw[h]
      _   = -1      := by norm_num
