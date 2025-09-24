/- 19 - Reductio Ad Absurdum

Given thes two facts about natural numbers a and b.

  (a > 5) → (b = 6)

  b = 6

show that:
  ¬a = 5

Solution:
     a > 5 → b = 6          given fact
          b = 6             given fact

          ¬a = 5            proof objective

      assume a = 5          for contradiction
             b = 6          using (1)
               != 5         arithmetic

      (4) contradicts (2)   (3) must be false
-/

import Mathlib.Tactic

example {a b : ℕ} (h1: a > 5  ↔  b = 6) (h2 : b = 6) : ¬ a = 5 := by
  by_contra g1
  apply h1.mpr at h2
  have g2 : ¬ a > 5 := by linarith
  contradiction
