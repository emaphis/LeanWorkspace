--  1.7. Additional Conveniences

-- 1.7.1. Automatic Implicit Parameters

--  It's not tyopically necessary to list all implicit parameters.

--  Implicit type parameter
def length' {α : Type} (xs : List α) : Nat :=
  match xs with
  | []  => 0
  | _ :: ys => Nat.succ (length' ys)

#eval length' ([] : List Nat)  --  0
#eval length' [1, 2, 3]   --  3

--  Type can be infered
def length (xs : List α) : Nat :=
  match xs with
  | []  => 0
  | _ :: ys => Nat.succ (length ys)

#eval length ([] : List Nat)  --  0
#eval length [1, 2, 3]   --  3


--  1.7.2. Pattern-Matching Definitions

--  Don't need to name parameters in functionds defined
--  by pattern matching
def lengthPM : List α -> Nat
  | []  => 0
  | _ :: ys => Nat.succ (lengthPM ys)

#eval lengthPM ([] : List Nat)  --  0
#eval lengthPM [1, 2, 3]   --  3


--  Pattern matching function that takes more than one argument
def drop : Nat -> List α -> List α
  | Nat.zero, xs => xs
  | _, []  => []
  | Nat.succ n, _ :: xs => drop n xs

#eval drop 0 [1, 2, 3]  --  [1, 2, 3]
#eval drop 2 [1, 2, 3]  --  [3]
#eval drop 3 [1, 2, 3]  --  []


--  Named arguments and patterns can also be used in the same definition.
--  a function that takes a default value and an optional value,
--  and returns the default when the optional value is none

def fromOption (default : α) : Option α -> α
  | none => default
  | some x => x

#eval fromOption "" (some "salmonberry")  -- "salmonberry"
#eval fromOption "" none                  --  ""

-- This function is already defined as `Option.getD`
#eval (some "salmonberry").getD ""  --  "salmonberry"
#eval none.getD ""                  --  ""


--  1.7.3. Local Definitions
def unzip' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip' xys).fst, y :: (unzip' xys).snd)

#eval unzip' [(1,'a'), (2,'b'), (3,'c')]  --  ([1, 2, 3], ['a', 'b', 'c'])

--  But unzip' is call twice for each recursion which is quadratic behaviour

--  Fix using local definitions
def unzip'' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip'' xys
    (x :: xs, y :: ys)

  #eval unzip'' [(1,'a'), (2,'b'), (3,'c')]  --  ([1, 2, 3], ['a', 'b', 'c'])

--  If `let` is recursive it must include the `rec` keyword.
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

#eval reverse [1, 2, 3, 4]  --  [4, 3, 2, 1]


--  1.7.4. Type Inference

def unzipTI : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzipTI xys
    (x :: unzipped.fst, y :: unzipped.snd)  --  no annotation needed

  #eval unzipTI [(1,'a'), (2,'b'), (3,'c')]  --  ([1, 2, 3], ['a', 'b', 'c'])


--  Omitting the return type for unzip is possible when using an explicit match expression

def unzipTI' (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzipTI' xys
    (x :: unzipped.fst, y :: unzipped.snd)  --  no annotation needed

  #eval unzipTI' [(1,'a'), (2,'b'), (3,'c')]  --  ([1, 2, 3], ['a', 'b', 'c'])


--  Somtime explicit types can work better even for built-in types.
--  14 can be a Nat or an Int:

#check 14  --  14 : Nat   - most specific type
#check (14 : Int)  -- 14 : Int  - If you specifically want an Int.


--  Missing type information can give confusing error messages:
/-
def unzipC pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzipC xys
    (x :: unzipped.fst, y :: unzipped.snd)

invalid match-expression, pattern contains metavariables
  []
-/
--  A “metavariable” is an unknown part of a program, written ?m.XYZ in error messages

--  Simple definitions can require type annotations:

def id1 (x : α) : α := x

def id2 (x : α) := x

-- but
--def id3 x := x
--  failed to infer binder type
--  failed to infer definition typ


--  1.7.5. Simultaneous Matching

def drop' (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys  => ys
  | _, []  => []
  | Nat.succ n, _y :: ys  => drop' n ys

#eval drop' 3 [1,2,3,4]  --  [4]


--  Example where the logical connection between `xs` and `x :: xs'`
--  is obscured by an intervening term.
/-
def sameLength' (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], [])  => true
  | (x :: xs', y :: ys') => sameLength' xs' ys'
  | _  => false

fail to show termination for
  sameLength'
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength':
  it is unchanged in the recursive calls
Not considering parameter β of sameLength':
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength' xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength' xs' ys'

Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             xs ys
1) 167:28-47  ?  ?
Please use `termination_by` to specify a decreasing measure.
-/

--  Simultaneously matching both lists is accepted:
def sameLength' (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], []  => true
  | _ :: xs', _ :: ys' => sameLength' xs' ys'
  | _, _  => false

#eval sameLength' [1,2,3] ['1', '2', '3']  --  true
#eval sameLength' [1,2,3] ['1', '2']  --  false


--  1.7.6. Natural Number Patterns

def even' (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even' k)

#eval even' 4  --  true
#eval even' 5  --  false

--  Like Lists Natural Numbers have special pattern matching syntax

def even : Nat -> Bool
  | 0 => true
  | n + 1 => not (even n)

#eval even 4  --  true
#eval even 5  --  false


--  The explicit patterns in halve, which divides a Nat by two and drops the remainder:
def halve' : Nat -> Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve' n + 1

#eval halve' 5  --  2
#eval halve' 4  --  2

-- an be replaced by numeric literals and +:
def halve : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

#eval halve 0  --  0
#eval halve 5  --  2
#eval halve 4  --  2

--  The patten matching syntax is not communative
/-
def halve'' : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve'' n + 1  --  not communative

invalid patterns, `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching
  .(Nat.add 2 n)
-/


--  1.7.7. Anonymous Functions

#check fun x => x + 1
--  fun x => x + 1 : Nat → Nat

#check fun (x : Int) => x + 1
--  fun x => x + 1 : Int → Int

--  Anonymous functions can be applied in precisely the same way as functions

#eval (fun x => x + x) 5  -- 10


--  lambda expression also support patterns

#check fun
  | 0 => none
  | n + 1 => some n
--match x with
--  | 0 => none
--  | n.succ => some n

--  `def`s can be written as lambdas
def double : Nat -> Nat := fun
  | 0 => 0
  | k + 1 => double k + 2

#eval double 4  --  8


--  Shorthand lambda notation

#eval (· + 1) 5  --  6

#check (· + 5, 3)  --  fun x => (x + 5, 3) : Nat → Nat × Nat
#eval (· + 5, 3) 6  --  (11, 3)

#eval (· * 2) 5  --  10


--  1.7.8. Namespaces

--  Namespace is a collection of names

--  Names can be placed in Namespace

def Nat.double (x: Nat) : Nat := x + x

#eval (4 : Nat).double  --  8

--  A sequence of declaration defining a new Namespace

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat  := 2 * x + 2 * x
end NewNamespace

--  To refere to them use the prefix:

#check NewNamespace.triple  --  NewNamespace.triple (x : Nat) : Nat
#check NewNamespace.quadruple  --  ewNamespace.quadruple (x : Nat) : Nat

#eval NewNamespace.triple 9  --  27

--  Namespaces can be opened

def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

#eval timesTwelve 3  --  36

open NewNamespace in
#check quadruple
--  NewNamespace.quadruple (x : Nat) : Nat


--  1.7.9. if let

--  When consuming values that have a sum type, it is often the case that only a single constructor is of interest.

--   given this type that represents a subset of Markdown inline elements:
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

--  a function that recognizes string elements and extracts their contents can be written:
def Inline.string?  (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _  => none

#eval Inline.string? (Inline.string "hello")  --  some "hello"


def Inline.stringA?  (inline : Inline) : Option String :=
  if let Inline.string s  := inline then
    some s
  else none

#eval Inline.stringA? (Inline.string "hello")  --  some "hello"


--  1.7.10. Positional Structure Arguments

--  Constructors

structure Point where
  x : Int
  y : Int

--  The constructor can be called directly, as in Point.mk 1 2.
#eval Point.mk 1 2  --  { x := 1, y := 2 }

--  Brace notation can be used to create a literal.
#check ({ x := 1, y := 2 } : Point)  --  { x := 1, y := 2 } : Point

--  Positionallt constructed

#eval ( ⟨1, 2⟩ : Point )  --  { x := 1, y := 2 }


--  1.7.11. String Interpolation

#eval s!"three fives is {NewNamespace.triple 5}"  --  "three fives is 15"

--  Cant interpoate a function literal
/-
#check s!"three fives is {NewNamespace.triple}"

failed to synthesize
  ToString (Nat → Nat)
-/
