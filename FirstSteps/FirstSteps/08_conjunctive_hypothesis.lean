-- 08 - Conjunctive "and" Hypothesis

import Mathlib.Tactic

/-
- Looked at a 'logical or; hypothesis
- Here we'll look at a "logical and" hypothesis.

∧ means "logical and"
P ∧ Q means both P and Q are true
- called conjunctions
proof are like earlier but with two hypotheses.

Given:
  (x = 5) ∧ (y = x + 3)

Prove
  y = 8

Where x, y : ℤ

Solve:
  (x = 5) ∧ (y = x + 3)   given fact.

    x = 5                 derived fact (1)
    y = x + 3             derived fact (1)

    y = x + 3             using fact (3)
      = (5) + 3           using fact (2)
      = 8                 using arithmetic
-/
example {x y : ℤ} (h : x = 5 ∧ y = x + 3) : y = 8 := by
  obtain ⟨ ha , hb ⟩ := h
  calc
    y = x + 3   := by rw [hb]
    _ = (5) + 3 := by rw [ha]
    _ = 8 := by norm_num
