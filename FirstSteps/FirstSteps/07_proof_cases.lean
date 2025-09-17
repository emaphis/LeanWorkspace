-- 07 - Proof By Cases

import Mathlib.Tactic


/-
A proof by cases deivides a task into separate cases.
... and proves each one leads to the desired conclusion.

Given:
  (x = 3) ∨ (x = -3)

Prove:
  x^2 = 9

Where x : ℝ
 ∨ is logical or
 P ∨ q means either P is true or Q is true or both are true
-- disjucntions

Break the hypothosis into two

Solution:
  (x = 3) ∨ (x = -3)    Given fact

case x = 3              using fact (1)
  x^2 = (3)^2           using case (2)
      = 9               using math

case x = -3             using fact (1)
  x^2 = (-3)^2          using case (3)
      = 9               using math
-/

example {x : ℤ} (h : x = 3 ∨ x = -3) : x^2 = 9 := by
  obtain ha | hb := h
  · calc
      x^2 = (3)^2 := by rw [ha]
      _ = 9 := by norm_num
  · calc
      x^2 = (-3)^2 := by rw [hb]
      _ = 9 := by norm_num

-- obtain ha | hb : h1
-- . calc
--    ...
-- . calc
--     ...
