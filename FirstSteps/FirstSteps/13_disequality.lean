-- 13 - Disequality

import Mathlib.Tactic

-- Given a natural number n < 5, show that
--        n ≠ 5

/-
Mathlib contains many *lemmas* and *theorems* we can use

Use lemmas to support a simple disequality proof.

n ≠ 5 is a disequality
n < 5 is an inequalty

Given a, b : ℕ, if a < b is true, then a ≠ b
This is a lemma in Lean

If we can show that n < 5, then we can conclude that n ≠ 5, using that lemma


Solution:

  n < 5             hypothesis
  n ≠ 5             proof objective

  a < 5 => a ≠ b    existing lemma

    n < 5           sufficient goal, by lemma (3)
    n < 5           using (1)

    n < 5 => n ≠ 5  by lemma (3)
-/

example {n : ℕ} (h: n < 5) : n ≠ 5 := by
  apply ne_of_lt
  exact h
