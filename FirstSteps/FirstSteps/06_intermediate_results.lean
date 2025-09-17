-- 06 - Intermediate Results

import Mathlib.Tactic

-- Prove a = 2 given a = b+1 and a = 2 with a,b as Z integers

/-
Proof with more sturcture than simple direct calculation.

Derive and intermediate result we use later in the full proof.

Given:
  a = b + 1
  b - 1 = 0

Prove:
  a = 2

Where a, b : Z

Solve:
  a = b + 1         Given fact
  b - 1 = 0         Given fact

  b - 1 = 0         using fact (2)
      b = 1         adding 1 to both sides

      a = b + 1     using fact (1)
        = (1) + 1   using intermediate result (3)
      a = 2         using arithmetic
-/

example {a b : ℤ} (h1 : a = b + 1) (h2 : b - 1 = 0) : a = 2 :=
  have h3: b = 1 := by linarith [h2]
  calc
    a = b + 1   := by rw [h1]
    _ = (1) + 1 := by rw [h3]
    _ = 2 := by norm_num

-- Intermediate results with `have` clause
-- Add 1 to both sides with `linarith` tactic
