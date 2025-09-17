--  3.1. Positive Numbers

--   datatype that represents only positive numbers.
inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

/-
def seven : Pos := 7
failed to synthesize
  OfNat Pos 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above
-/

--  Use constuctors
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

--   addition and multiplication are not easy to use:
/-
def fourteen : Pos := seven + seven
failed to synthesize
  HAdd Pos Pos ?m.272

def fortyNine : Pos := seven * seven
failed to synthesize
  HMul Pos Pos ?m.272
-/


--  3.1.1. Classes and Instances

class Plus (α : Type) where
  plus : α -> α -> α

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 5 3  --  8

--  namespace

open Plus (plus)

#eval plus 5 3  --  8


--  Defining pos

def Pos.plus : Pos -> Pos -> Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven

#eval fourteen


--  No instance of `Plus Float`
/-
#eval plus 5.2 917.25861
failed to synthesize
  Plus Float
-/


--  3.1.2. Overloaded Addition

instance : Add Pos where
  add := Pos.plus

def fourteen' : Pos := seven + seven

#eval fourteen'


--  3.1.3. Conversion to Strings

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"
--  "There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"

--  Converting Pos to Nat
def Pos.toNat : Pos -> Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"
--  "There are 7"


--  3.1.4. Overloaded Multiplication

def Pos.mul : Pos -> Pos -> Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [ seven * Pos.one,
        seven * seven,
        Pos.succ Pos.one * seven ]

--  [7, 49, 14]


--  3.1.5. Literal Numbers

class Zero' (α : Type) where
  zero' : α

-- There should be no instances of Zero Pos.

class One (α : Type) where
  one : α

instance : One Pos where
  one := Pos.one

class OfNat' (α : Type) (_ : Nat) where
  ofNat : α

--  With this instance 1 can be used of Pos.one
#eval (1 : Pos)
