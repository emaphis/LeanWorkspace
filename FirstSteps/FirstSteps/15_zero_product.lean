-- 15 - Zero Product

import Mathlib.Tactic

-- Given the zero product
--      (p - 1) · (q - 2) = 0
-- Show that p = 1 or q = 2
-- Where p and q are rational numbers

/-
Some lemmas are bideirectional implications <==>

To apply them we decide which of the two directions mathc our task

It's common knowledte that the product of two numbers is zero iff
one or the other is zero

We think of this as a lemma:
  a · b <==> (a = 0) ∨ (b = 0)

P <==> Q is *equivalent* to both of the following being true

  p ==> Q
  Q ==> P

We say "P is true *if and only if* Q is true"

  "P is true iff Q is true"

Our lemma is equivalent to the following two statements:

  a · b = 0 ==> (a = 0) ∨ (b = 0)

  (a = 0) ∨ (b = 0)  ==> a · b = 0

The antecedent of the first matches out hypothesis
(p - 1) · (q - 2) = 0 so applying gives us a disjunction.

  (p - 1 = 0) ∨ (q - 2 = 0)

We could conclude that p = 1 or q = 2 by inpection, but lean needs more detail

Solution
  (p - 1) · (q - 2) = 0             hypothesis

  a · b = 0 ==> (a = 0) ∨ (b = 0)   existing lemma

  (p - 1 = 0) ∨ (q - 2 = 0)         apply (2) to (1)

  case p - 1 = 0                    using (2)
          p = 1                     add 1 to both sides

  case q - 2 = 0                    using (3)
          q = 2                     add 2 to both sides

      (p = 1) ∨ (q = 2)             conclusion
-/

example {p q : ℚ} (h: (p - 1) * (q - 2) = 0) : p = 1 ∨ q = 2 := by
  apply mul_eq_zero.mp at h
  obtain hp | hq := h
  · left
    linarith
  · right
    linarith

-- Mathlab lemma: mul_eq_zero => a · b = 0 <==> (a = 0) ∨ (b = 0)

--theorem mul_eq_zero' : a * b = 0 <==> a = 0 ∨ b 0 :=
