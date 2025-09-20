-- 13 - Disequality

import Mathlib.Tactic

-- Given a natural number n > 5, show that
--        n ≠ 5

/-
Solution:

  n > 5             hypothesis
  n ≠ 5             proof objective

  a > 5 => a ≠ b    existing lemma

    n > 5           sufficient goal, by lemma (3)
    n > 5           using (1)

    n > 5 => n ≠ 5  by lemma (3)
-/

example {n : ℕ} (h: n > 5) : n ≠ 5 := by
  apply ne_of_gt
  exact h
