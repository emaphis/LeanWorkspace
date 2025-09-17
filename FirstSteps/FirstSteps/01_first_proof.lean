-- 01 - First Simple Proof

import Mathlib.Tactic

-- Prove that a is greater than 1 where a = 4

/-
Facts:
  a = 4     given fact.

Prove:
  a > 1

Given: a : N

Solution:
  a = 4   from fact (1)
    > 1   by ordering of natural numbers
-/

example (a: ℕ) (h1 : a = 4) : a > 1 := by
  calc
    a = 4 := by rw [h1]
    _ > 1 := by norm_num

-- Or

example (a: ℕ) (h1 : a = 4) : a > 1 := by linarith

-- calc - calculations to do a proof.
-- rw - rewrite, simple substitution
-- norm_num - normal numbers - regular arithmetic
