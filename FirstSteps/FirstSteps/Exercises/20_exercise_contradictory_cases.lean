/- 20 - Contradictory Cases

show P → ¬ (¬ P)
-/

import Mathlib.Tactic

example {P : Prop} :  P → ¬(¬P) := by
  intro g
  by_cases h1: ¬P
  · contradiction
  · exact h1
