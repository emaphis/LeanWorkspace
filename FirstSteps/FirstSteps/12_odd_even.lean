-- 12 - Odd & Even
-- Using Definitions Odd Numbers

import Mathlib.Tactic

-- Show the integer 13 is odd.

/-
There is a huge body of commonly agreed knowledge that
mathematicion refer to in their own proof.

Lots of these *lemma, theorems, and definitions* are in Mathlib

To show 13 is odd, we need to show it meets the *definition* of odd.

  An *odd* integers is an integers such thatn 2K + 1, where k is an integer.

  If *there exists* and integer k *such that* n = 2k +1 then n is odd

  Proof:
  Existence proof.d

  if we can find an integer k such that 13 = 2k + 1 then 13 is odd.

Solution:
  13 is odd                           proof objective

  ∃k << ℤ[n = 2k + 1] ==> n is odd    definition of odd

  ∃k << ℤ[13 = 2k + 1]                sufficient goal using (1)

    use k = 6                         chosen example
            13 = 2K + 1               using (2)

    13 = 2(6) + 1                     by definition (1)

-/

example : Odd (13 : ℤ) := by
  dsimp [Odd]
  use 6
  norm_num


-- Odd is a function that takes a number and outputs a propostion involving that number
def Odd' (a : ℤ) : Prop := ∃ k, a = 2 * k + 1

#check Odd' 13
