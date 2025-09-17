# Notes for "Maths Proofs in Lean: First Steps"

etting started site: <https://www.youtube.com/@LeanFirstSteps>

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
