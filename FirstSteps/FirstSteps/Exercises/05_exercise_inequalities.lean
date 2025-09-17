-- 05 - Simple Inequality Proof

import Mathlib.Tactic

-- Prove a < c of we know a < b ad b <= c, where a,b,c are Natureals

example {a b c : ℕ} (h1 : a < b) (h2 : b <= c) : a < c := by
  calc
    a < b := by rel [h1]
    _ ≤ c := by rel [h2]
