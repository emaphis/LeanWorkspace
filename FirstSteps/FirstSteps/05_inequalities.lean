-- 05 - Simple Inequality Proof

import Mathlib.Tactic

/-
We have an inequality in the hypothesis of the theorem
we want to prove

- Allows more general theorms.

Given:
    b = a^2
    a ≥ 2

Show that:
    b ≥ 4

Where a, b : ℕ

Solve:
    b = a^2     given fact
    a ≥ 2       given fact

    b = a^2     using fact (1)
      ≥ (2)^2   using fact (2)
      = 4       using arithmetic
-/

example {a b : ℕ} (h1 : b = a^2) (h2 : a ≥ 2) : b ≥ 4 := by
  calc
    b = a^2 := by rw [h1]
    _ ≥ (2)^2 := by rel [h2]
    _ ≥ 4 := by norm_num

-- dont forget to use `rel` for relations.
