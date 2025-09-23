/- 18 - Our Own Definition
    Square  numbers

in general, the nth tirangle numbe is:  n · n

Our task is to create a definition of square numbers that is
a propsition

    True only if supplied numbes is a square number.

A propositoon for a square number 'S' could be:

    ∃(n: ℕ) | S = n · n  |

This propostion is only true if 'T' is a triangle number

    Tbat is if 'S' can be express in the form of `n · n` for
    some natural number 'n'.

    ∃(n: ℕ) | S = n · n |
-/

import Mathlib.Tactic

def Square (a: ℕ) : Prop := ∃ n, a = n * n
--  /name   /variable/Type  S /definition


example : Square 1 := by
    dsimp [Square]
    use 1


example : Square 16 := by
    dsimp [Square]
    use 4

example : Square 100 := by
    dsimp [Square]
    use 10
