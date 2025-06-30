--  Interlude: Propositions, Proofs, and Indexing

--  Use square for indexing into arrays.

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

--  Individual components can be extracted:

def hedgehog := woodlandCritters[0]
def deer  := woodlandCritters[1]
def snail  := woodlandCritters[2]

#eval [hedgehog, deer, snail]
--  ["hedgehog", "deer", "snail"]

/-
--  attempting to extract the fourth element results in a compile-time error
def oops := woodlandCritters[3]

failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < woodlandCritters.length
-/


--  Propositions and Proofs

--  Exampls of propositions
--  Propostions are statements that can be true or false.

--  1 + 1 = 2
--  Addition is commutative.
--  1 + 1 = 15
--  Paris is the captial of France
--  Buenos Aires is the captical of South Korea
--  All birds can fly.

-- Nonsense statments are not popositions

--  1 + green = ice cream
--  All captial cites are primary numbers
--  At leas one gorge is a fleep.

--  A proof is a convincing argument that a proposition is true.

--  the proposition 1+1=2 can be written directly in Lean.
def onePlusOneIsTwo' : 1 + 1 = 2 := rfl  -- proved by `reflexivity (rfl)`

/-
--  But `rfl` can not proove the false propsition 1 + 1 = 15:
def onePlusOneisFifeteen : 1 + 1 = 15 := rfl

type mismatch
  rfl
has type
  ?m.1247 = ?m.1247 : Prop
but is expected to have type
  1 + 1 = 15 : Prop
-/

--  The prior example could be rewritten as a `theorem`

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl


--  Tactics

--  `Proofs` are normally written using `tactics`, rather than by providing `evidence`
--  `Tactics` are small programs that construct evidence for a proposition.

--  To write a proof with tactics, begin the definition with `by`
--  Writing `by` puts Lean into tactic mode
theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  decide

--  `decide`  tactic invokes a decision procedure, which is a program
--   that can check whether a statement is true or false,

--  `simp` is simplify.


--  Connectives
--  Using ∧ and ∨ to connect propostions

theorem andAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

#check And.intro
--  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide

theorem notTwoEqualFive : ¬ (1 + 1 = 5) := by decide

theorem trueIsTrue : True := by decide

theorem trueOrFalse : True ∨ False := by decide

theorem falseImpliesTrue : False → True := by decide


--  Evidence as Arguments

/-
def third (xs : List α) : α := xs[2]

failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.5379
xs : List α
⊢ 2 < xs.length
-/

--  the obligation to show that the list has at least three entries can be
--  imposed on the caller by adding an argument that consists of evidence
--  that the indexing operation is safe:

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by decide)  --  "snail"


--  Indexing Without Evidence

-- Using Option

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters  --  some "snail"
#eval thirdOption ["Only", "two"]   --  none

--  crashes if the index is out of bounds
#eval woodlandCritters[1]!  --  "deer"


--  Messages You May Meet

/-
--  Decide can prove an array option is false
#eval third ["rabit"] (by decide)

tactic 'decide' proved that the proposition
  ["rabit"].length > 2
is false
-/

/-
--  The simp and decide tactics do not automatically unfold definitions with def.

theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp

--  simp made no progress

theorem onePlusOneIsStillTwo' : OnePlusOneIsTwo := by decide

failed to synthesize
  Decidable OnePlusOneIsTwo
-/

/-
-- polymorphic functions that use unsafe indexing may produce the following message:
def usafeThird (xs : List α) : α := xs[2]!

failed to synthesize
  Inhabited α
-/

/-
--  Adding whitespace between a list and the brackets used for lookup can cause another message

#eval woodlandCritters [1]

function expected at
  woodlandCritters
term has type
  List String
-/


--    Exercises

theorem onePlusOneAndLessThan' : 1 + 1 = 2 ∨ 3 < 5 := by decide


--  Prove the following theorems using rfl:

theorem twoPlusThreeIsFive : 2 + 3 = 5 := by rfl
theorem fifeteenMinsEightIsSeven  : 15 - 8 = 7 := by rfl
theorem helloWorld : "Hello, ".append "world" = "Hello, world" := by rfl
/-
theorem fiveIsLessthaEighteen : 5 < 18 := by rfl
tactic 'rfl' failed, the left-hand side
  5
is not definitionally equal to the right-hand side
  18
⊢ 5 < 18
-/

--  Prove the following theorems using by decide:

theorem twoPlusThreeIsFiveD : 2 + 3 = 5 := by decide
theorem fifeteenMinsEightIsSevenD : 15 - 8 = 7 := by decide
theorem helloWorldD : "Hello, ".append "world" = "Hello, world" := by decide

theorem fiveIsLessthaEighteen : 5 < 18 := by decide  --  What?


--  Write a function that looks up the fifth entry in a list.
--  Pass the evidence that this lookup is safe as an argument to the function.

def fifth (xs : List α) (ok : xs.length > 5) : α := xs[5]

def good : List Nat := [1,2,3,4,5,6]
def short : List Int := [1,2]
def empty : List Int := []

#eval fifth good (by decide)  --  6

/-
#eval fifth short (by decide)
tactic 'decide' proved that the proposition
  short.length > 5
is false

#eval fifth empty (by decide)
tactic 'decide' proved that the proposition
  short.length > 5
is false
-/
