/- 18 - Our Own Definition
    Triangle  numbers

in general, the nth tirangle numbe is:
    n · (n + 1)
    ------------
         2

Our task is to create a definition of triangle numbers that is
a propsition

    True only if supplied numbes is a triangle number.

A propositoon for a triangle number 'T' could be:

    ∃(n: ℕ) | T = (n · (n + 1)) / 2 |

This propostion is only true if 'T' is a triangle number

    Tbat is if 'T' can be express in the form of ` (n · (n + 1)) / 2` for
    some natural number 'n'.

    ∃(n: ℕ) | 2T = n · (n + 1) |
-/

import Mathlib.Tactic

def Triangle (a: ℕ) : Prop := ∃ n, 2*a = n * (n + 1)
--  /name   /variable/Type  S /definition


example : Triangle 1 := by
    dsimp [Triangle]
    use 1


example : Triangle 10 := by
    dsimp [Triangle]
    use 4
