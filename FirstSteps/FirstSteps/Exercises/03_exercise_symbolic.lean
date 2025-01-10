-- 03 - Symbols, No Numbers

import Mathlib.Tactic

-- Prove that z = x where z = y and y = x, where x,y,z are Reals

example {x y z : ℝ} (h1 : z = y) (h2: y = x) : z = x :=
  calc
    z = y := by rw [h1]
    _ = x := by rw [h2]
