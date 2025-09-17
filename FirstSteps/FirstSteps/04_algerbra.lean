-- 02 - Simple Algerbra

import Mathlib.Tactic

-- Prove z where y = y^2 and y = x + c

/-
Given:
   z = y^2
   y = x + c

Prove:
  z = x^2 + c^2 + 2*x*c

Solution:
  z = y^2         given (1)
    = (x + c)^2   given (2)
    = x^2 + c^2 + 2*x*c  by algerbra
-/

example {x y z c: ℝ} (h1 : z = y^2) (h2: y = x + c) : z = x^2 + c^2 + 2*x*c :=
  calc
    z = y^2 := by rw [h1]
    _ = (x + c)^2 := by rw[h2]
    _ =  x^2 + c^2 + 2*x*c := by ring


-- Prove y = a^2 - b^2 where y = (a-b)(a+b) and y, a, b are Reals

/-
Prove:
  (a + b)(a - b) = a^2 - b^2

a and b are integers (N)

Solution:
  (a + b) * (a + b) = a^2 - a.b + b.a - b^2  by algerbra
          = a^2 - b^2              by algerbra
-/

example {a b : ℝ} : (a - b) * (a + b)  = a^2 - b^2 :=
  calc
    (a - b) * (a + b) = a^2  - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring

-- Ring tactic for simple algerbra.
