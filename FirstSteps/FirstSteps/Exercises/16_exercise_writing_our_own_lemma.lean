
/- 16 - Writing Our Own Lemma -/

import Mathlib.Tactic

/-
Let's create a lemma for natural numbers a and b
    a ≤ b ∨ b + 1 <= a

Example: setting b = 7 lemma says a ≤ 7 or a ≤ a

Solution:

    a ≤ ∨ b + 1 ≤ a     proof objected a, b : ℕ

    a + 1 ≤ b ↔ a < b   known lemma, a. b : ℕ
    a ≤ b ∨ b < a       known lemma, a, b : ℕ0

    a ≤ b ∨ b + 1 ≤ a   apply lemma (2) to (1)

lemma (1) is close to the proof objective

lemma (2) lets us rewrite b < a as b + 1 ≤ a, which gives
 us the proof objective

Both lemmas (1) and (2) exist in Mathlib
-/

lemma Nat.le_or_succ_le (a b: ℕ) : a ≤ b ∨ b + 1 ≤ a := by
    rw [Nat.add_one_le_iff]
    exact le_or_gt a b


example {c : ℕ} : c ≤ 2 ∨ 3 ≤ c  := by
    exact Nat.le_or_succ_le c 2
