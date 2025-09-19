-- 10 - "And" Goal - conjunction

import Mathlib.Tactic

-- For integer x, given that x = -1, show that
--      (x^2 = 1) ∧ (x^3 = -1)

/-
P ∧ Q true means that *both* P and Q must be true
So we have to prove both x^2 and x^3 = -1

  x = -1                    given fact
  (x^2 = 1) ∧ (x^3 = -1)    proof objective

  x^2 = (-1)^2              using fact (1)
      = 1                   using arithmetic

  x^3 = (-1)^3              using fact (1)
      = - 1                 using arithmetic

  (x = -1) ==> (x^2 = 1) ∧ (x^3 = -1)  using results (2,3)
-/

example {x : ℤ} (h: x = -1) : x^2 = 1 ∧ x^3 = -1 := by
  constructor
  · calc
      x^2 = (-1)^2  := by rw[h]
      _   = 1       := by norm_num
  · calc
      x^3 = (-1)^3  := by rw[h]
      _   = -1      := by norm_num
