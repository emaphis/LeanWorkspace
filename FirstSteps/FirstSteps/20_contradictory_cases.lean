/- 20 - Contradictory Cases

- In proof by cases each case lead to the proof objective.

- In general, not all cases permitted by hypotheis lead to the proof
  objective

- Some cases may lead to a contradiction, rulling them out
  as possible cases.

Task:
  If P is a propositon, show that:

    ¬(¬P) → P

  For this task we'll pretend  we don't yet know that two necations
  cancel out.

  Proving ¬(¬P) → P will justify our intuition that two necotiatns od
  indead cancel out.


Law of Excluded Middle

  A propostion is either true or false, there is no other possibliey

  This ica called the Law of Excluded Middle

  So there are only two possiblities for our proposition P, true of false.


Solution:
  ¬(¬P) → P         proof objective

    ¬(¬P)           hypothesis
    P               proof goal

    P∨¬P            law of excluded midle

  case P            using fact (3)
    P               proof goal

  case ¬P           using fact (3)
    ¬P              contradictory hypothesis (1)

  ¬(¬P) → P         only consistent case
  -/

import Mathlib.Tactic

example {P : Prop} : ¬(¬P) → P := by
  intro g
  by_cases h: P
  · exact h
  · contradiction
