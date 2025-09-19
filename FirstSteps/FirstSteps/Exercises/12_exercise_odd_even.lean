-- 12 - Odd & Even
-- Using Definitions Odd Numbers

import Mathlib.Tactic

-- Show the integer 13 is even.

/-
Solution:
  13 is even                          proof objective

  ∃r << ℤ[n =  r + r] ==> n is even   definition of odd

  ∃r << ℤ[14 =  r + r]                sufficient goal using (1)

    use r = 7                         chosen example
      14 = r + r                      using (2)

      14 = (7) + (7)                   by definition (1)

-/

example : Even (14 : ℤ) := by
  dsimp [Even]
  use 7
  norm_num
