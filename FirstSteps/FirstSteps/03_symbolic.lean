-- 03 - Symbols, No Numbers

import Mathlib.Tactic

-- Prove that z = (x+2)^2 where z = y^2 and y = x + c

/-
Facts:
  x = y^2
  y = x + c

Prove:
  z = (x + c)^2

Given: x y z c are Reals

Solution:
  x = y^2     given fact (1)
  y = x + c   given fact (2)

  z = y^2         using fact (1)
    = (x + c)^2   substitution using fact (2)
-/

example {x y z c: ℝ} (h1 : z = y^2) (h2: y = x + c) : z = (x + c)^2 :=
  calc
    z = y^2 := by rw [h1]
    _ = (x + c)^2 := by rw [h2]
