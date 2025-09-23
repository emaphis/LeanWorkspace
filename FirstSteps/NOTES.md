# Notes for "Maths Proofs in Lean: First Steps"

Getting started videos: <https://www.youtube.com/@LeanFirstSteps/videos>

GitHub repository: <https://github.com/rzeta0/Lean-First-Steps>

Blog: <https://leanfirststeps.blogspot.com/>

## Part I - Direct proofs

01 - First Proofs

-- calc - calculations to do a proof.

-- rw - rewrite, simple substitution

-- norm_num - normal numbers - regular arithmetic

02 - Sustitution and calculation

03 - Symbols, No Numbers

04 - Simple Algebra

-- ring -  Tactic of communtative rings - Algerbra

05 - Inequalities

-- rel - tactic for solveing relations and inequalities

## Part II - Structured Proofs

06 - Intermediate Results

-- intermediate results with the `have` clause

-- `linarith` tactic - Math on both sides of the equation(?)

07 - Proof By Cases

``` lean
obtain ha | hb := h1
. calc
    ...
. calc
    ...
```

08 - "And" Hypothesis

09 - "Or" Goal

```lean
    left
    calc
        ...

-- `left` select left part of goal, `right` selects the rest of the goal
```

-- 10 - "And" Goal

```lean
 constructor
  · calc
      ...
  · calc
      ...
```

11 - Existence

## Part III - Definitions & Lemmas

12 - Odd & Even

using predifined propositons in proofs

- desimp  - simplifies an expression in the InfoView

Even / Odd - creates propositions to solve for even/odd properties of humbers

13 - Disequality

apply - applies a lemma or theorem to the current goal, changing or solving goal

exact -  applies a lemma or theorem exactly

Loogle <https://loogle.lean-lang.org/>

14 - Disequality Again

Lemma's applied to a hypothesis

apply at h

15 - Zero Product

```lean
Mathlab lemma: mul_eq_zero => a · b = 0 <==> (a = 0) ∨ (b = 0)
```

tactic.mp  -> modus penens

tactic.mpr -> modus.ponens reverse

16 - Writing Our Own Lemma

17 - Using Our Own Lemma

18 - Our Own Definition

```lean
def Triangle (a: ℕ) : Prop := ∃ n, 2*a = n * (n + 1)
--  /name   /variable/Type  S /definition
```
