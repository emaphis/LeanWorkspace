-- 01 - First Proof

import Mathlib.Tactic

-- Prove  a < 10 given a = 4. a is a Natural number
-- Tip: the norm_num tactice understands "<",
-- as well as '>'

example (a : ℕ) (h1 : a = 4) : a < 10 := by
  calc
    a = 4  := by rw [h1]
    _ < 10 := by norm_num
