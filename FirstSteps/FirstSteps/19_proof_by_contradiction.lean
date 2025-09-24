/- 19 - Reductio Ad Absurdum

Given thes two facts about natural numbers a and b.

  (a = 5) →s (b = 6)

  b = 7

show that:
  ¬a = 5

The symbol ¬ means `negation` amd reads "it is not the case that"

¬a = 5 reads "it is not the case thatn a = 5" or simply "a is not 5"

intuition:

  a = 5 → b = 6 tells us that if a = 5 then b = 6

  But b is 7 so:

  it can't be the case that a = 5

|    To prove a statement is false     |
| we show it leads to a contradiction  |

In symbols: to show ¬P we need to whow the staement P leats to
a contradiction

For out tast, P is a = 5. So, to show ¬a - 5 we need to show a = 5,
taken as a hypothesis, leads to a contradicton.

Solution:
     a = 5 → b = 6          given fact
          b = 7             given fact

          ¬a = 5            proof objective

      assume a = 5          for contradiction
             b = 6          using (1)
               != 7         arithmetic

      (4) contradicts (2)   (3) must be false

-/

import Mathlib.Tactic

example {a b : ℕ} (h1: a = 5 → b = 6) (h2 : b = 7) : ¬ a = 5 := by
  intro g
  apply h1 at g
  have h2x : ¬ b = 7 := by linarith
  contradiction
