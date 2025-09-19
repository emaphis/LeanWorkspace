-- 11 - Existence

import Mathlib.Tactic

-- Show *there exists* a natural numbe n, such that
--          n^2 + 1 = 10


/-
The aim of an existence proof is to show that something exists.

Proof objective
  ∃n ε ℕ[n^2 + 1 = 10]

  use n = 3               chosen example
    n^2 + 1 = (3)^2 + 1   using (1)
            = 10          by arithmetic
-/

example : ∃ n: ℕ, n^2 + 1 = 10 := by
  use 3
  calc
    3^2 + 1 = 10 := by norm_num

-- more concise version
example : ∃ n:ℕ, n^2 + 1 = 10 := by
  use 3
  norm_num
