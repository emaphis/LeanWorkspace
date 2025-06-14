--  1.6. Polymorphism

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
 { x := Nat.zero, y := Nat.zero }

 #eval natOrigin
 --  { x := 0, y := 0 }

def replaceX' (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check replaceX'
--  replaceX' (α : Type) (point : PPoint α) (newX : α) : PPoint α

-- curring to produce a specifically typed `replaceX`
#check replaceX' Nat
--  replaceX Nat : PPoint Nat → Nat → PPoint Nat

def replaceNat' := replaceX' Nat

#eval replaceNat' natOrigin 5
--  { x := 5, y := 0 }


inductive Sign where
  | pos
  | neg

--  A function whose argument is a Sign
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos  --  3


--  1.6.1. Linked Lists

def primesUnder10 : List Nat := [2, 3, 5, 7]

#eval primesUnder10  --  [2, 3, 5, 7]


-- defined like
inductive List' (α : Type) where
  | nil : List' α
  | cons : α -> List' α -> List' α


-- Using List's constructors 'cons'
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

#eval explicitPrimesUnder10
--  [2, 3, 5, 7]


-- Lists can be consumed by functions.

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length' α ys)

#eval length' String ["Sourdough", "bread"]  --  2

--  [] notation can be used in pattern matching.

def length'' (α : Type) (xs : List α) : Nat :=
  match xs with
  | []  => 0
  | _ :: ys => Nat.succ (length'' α ys)

#eval length'' String ["Sourdough", "bread"]  --  2


--  1.6.2. Implicit Arguments - Type parameters can be derived '{}'

def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX natOrigin 5  --  { x := 5, y := 0 }


def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => Nat.zero
  | _ :: ys => Nat.succ (length ys)

#eval length ["Sourdough", "bread"]  --  2

#eval length primesUnder10  --  4

--  Sometime type has to be explicitly passed.

#check List.length (α := Int)
--   List.length : List Int → Nat


--  1.6.3. More Built-In Datatypes

--  1.6.3.1. Option

inductive Option' (α : Type) : Type where
  | none : Option' α
  | some (val : α) : Option' α

-- May not be a head.
def List.head?' {α : Type} (xs : List α) : Option α :=
  match xs with
  | []  => none
  | y :: _ => some y

#eval primesUnder10.head?'  --  some 2

-- two erros:

--#eval [].head?
--  don't know how to synthesize implicit argument 'α' @List.nil
--  don't know how to synthesize implicit argument 'α'  @List.head?

--  So pass an explicit type
#eval [].head? (α := Int)  --  None

#eval ([] : List Int).head?  -- None


--  1.6.3.2. Prod
--  Joining two values together. - Pair, product

structure Prod' (α : Type) (β : Type) : Type where
  fst : α
  snd : β

-- Type Prod α β can be written as α × β
-- \ a  \ x  \ b  -> α × β

def fives' : String × Int := { fst := "five", snd := 5 }

-- so more concise
def fives : String × Int := ("five", 5)

-- () are right associative...
def sevens' : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))

-- All products of more than two type are actually nested products of two


--  1.6.3.3. Sum
--  A choice of different types

inductive Sum' (α : Type) (β : Type) : Type where
  | inl : α -> Sum' α β
  | inr : β -> Sum' α β

-- Cartesian produce notattion: \ o+ - ⊕

-- an example
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]

#eval animals
--  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

--  Pattern matching can be used to distinguish between the two constructors.
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | []  => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals  --  3


--  1.6.3.4. Unit

inductive Unit' : Type where
  | unit' : Unit'

--  Unit Unit in polymorphic code

inductive ArithExpr (ann : Type) : Type where
  | int : ann -> Int -> ArithExpr ann
  | plus : ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann
  | minus : ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann
  | times :  ann -> ArithExpr ann -> ArithExpr ann -> ArithExpr ann


--  1.6.3.5. Empty

--  1.6.3.6. Naming: Sums, Products, and Units
-- α β \ n κ ⊹


--  1.6.4. Messages You May Meet

--  Not all structures can have a type
/-
inductive MyType : Type where
  | ctor : (α : Type) -> α -> MyType

invalid universe level in constructor 'MyType.ctor', parameter 'α' has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
/-
inductive MyType' : Type where
  | ctor : (MyType' -> Int) -> MyType'

(kernel) arg #1 of 'MyType'.ctor' has a non positive occurrence of the datatypes being declared
-/

-- Recursive functions that take two parameters should not match against the pair, but rather match each parameter independently
/-
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _  => false

fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1763:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
-/

-- fixing the problem with nested pattern matichin.
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | _ :: xs' =>
    match ys with
    | _ :: ys' => sameLength xs' ys'
    | _ => false


  --  Forgetting an argument to an inductive type can also yield a confusing message.
/-
inductive MyType' (α : Type) : Type where
  | ctor : α -> MyType'

type expected, got
  (MyType' : Type → Type)
-/

inductive MyType (α : Type) : Type where
  | ctor : α -> MyType α

--  The same message can appear when type arguments are omitted in other contexts
/-
def ofFive : MyType := ctor 5

type expected, got
  (MyType : Type → Type)
-/
