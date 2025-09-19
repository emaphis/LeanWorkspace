-- 11 - Existence

import Mathlib.Tactic

-- Show *there exists* a natural numbe n, such that
--          n > 5


/-
The aim of an existence proof is to show that something exists.

Proof objective
  ∃n ε ℕ[n > 5]

  use n = 6               chosen example
    n > 5   using (1)
            = 10          by arithmetic
-/

example : ∃ n: ℕ, n > 5 := by
  use 6
  calc
    6 > 5 := by norm_num

-- more concise version
example : ∃ n: ℕ, n > 5 := by
  use 6
  norm_num
