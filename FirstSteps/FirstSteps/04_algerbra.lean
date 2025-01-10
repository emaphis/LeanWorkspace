-- 02 - Simple Algerbra

import Mathlib.Tactic

-- Prove z = x^2 + c^2 + 2*x*x where y = y^2 and y = x + c

example {x y z c: ℝ} (h1 : z = y^2) (h2: y = x + c) : z = x^2 + c^2 + 2*x*c :=
  calc
    z = y^2 := by rw [h1]
    _ = (x + c)^2 := by rw[h2]
    _ =  x^2 + c^2 + 2*x*c := by ring


-- Prove y = a^2 - b^2 where y = (a-b)(a+b) and y, a, b are Reals

example {a b : ℝ} : (a - b) * (a + b)  = a^2 - b^2 :=
  calc
    (a - b) * (a + b) = a^2  - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring
