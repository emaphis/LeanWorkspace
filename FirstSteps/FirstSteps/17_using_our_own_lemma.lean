/- 17 - Using Our Own Lemma
-/

import Mathlib.Tactic


lemma Nat.le_or_succ_le (a b: ℕ) : a ≤ b ∨ b + 1 ≤ a := by
    rw [Nat.add_one_le_iff]
    exact le_or_gt a b

/-
* For any natural number n, show that  n^2 ≠ 7

Proof strategy - split the number sequence into tow

    all the smaller number result in n^2 < 7

    all the larger numbers result in n^2 > 7

If every possible choice for n leads to either n^2 < 7 ∨ n^2 > 7
then n^2 ≠ 7

Solution:
    n ≠ 7               proof objective

    n ≤ 2 ∨ 3 ≤ n       lemma (1) with m = 2

    case n ≤ 2          using (2)
        n^2 ≤ 4
            < 7
        n^2 ≠ 7         lenna a < b → a ≠ b

    case n ≥ 3
        n^2 ≥ 9
            > 7
        n^2 ≠ 7         lemma a > b → a ≠ b

        n ≠ 7           conclusion of both cases
-/

example {n : ℕ} : n^2 ≠ 7  := by
    have h := Nat.le_or_succ_le n 2
    obtain ha | hb := h
    · apply ne_of_lt
      calc
        n^2 ≤ 2^2 := by rel [ha]
        _ < 7 := by norm_num
    · apply ne_of_gt
      calc
        n^2 ≥ 3^2 := by rel [hb]
        _ > 7 := by norm_num
