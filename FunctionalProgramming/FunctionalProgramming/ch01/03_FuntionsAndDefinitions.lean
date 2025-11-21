--  1.3. Functions and Definitions

def hello := "Hello"

--  Adding a typed value
def lean : String := "Lean"

--  Using it
#eval String.append hello (String.append " " lean)
--  "Hello Lean"

--  1.3.1. Defining Functions

def add1 (n : Nat) : Nat := n + 1

#eval add1 7  --  8

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k
  else n

#eval maximum (5 + 8) (2 * 7)  --  14

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval spaceBetween "hello" "John"  --  "hello John"


--  1.3.2. Defining Types

def Str : Type := String  -- Type alias

def aStr : Str := "This is a string"


--  1.3.2.1. Messages You May Meet

--  Longer natural number
def NaturalNumber : Type := Nat

-- def thirtyEight : NaturalNumber := 38

-- failed to synthesize
--  OfNat NaturalNumber 38
-- numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
--   NaturalNumber
-- due to the absence of the instance above

def thirtyEight : NaturalNumber := (38 : Nat)

-- abreviations

abbrev N : Type := Nat

def thirtyNine : N := 39
