-- 1.1 Evaluating Expressions
-- Exercises

-- Find the values (evaluate).

#eval 42 + 19  -- 61

#eval String.append "A" (String.append "B" "C")
-- "ABC"

#eval String.append (String.append "A" "B") "C"
-- "ABC"

#eval if 3 == 3 then 5 else 7  -- 5

#eval if 3 == 4 then "equal" else "not equal"
-- "not equal"

-- Done

--  1.3 Functions and Definitions

-- 1.3.1.1.

def joinStringsWith (sep : String) (str1 : String) (str2 : String) :=
  String.append str1 (String.append sep str2)

#eval joinStringsWith ", " "one" "and another"
-- "one, and another"

#check joinStringsWith ": "  --  String → String

def volume (height : Nat) (width : Nat) (depth : Nat) :=
  height * width * depth

#check volume
--  volume (height width depth : Nat) : Nat


--  1.4.3. Exercises
structure RectangularPrism where
  height : Float
  width  : Float
  depth  : Float
deriving Repr

def volume' (prism : RectangularPrism) : Float :=
  prism.height * prism.width * prism.depth


structure Point where
  x : Float
  y : Float
deriving Repr

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

structure Segment where
  end1 : Point
  end2 : Point
deriving Repr

def length  (seg : Segment) : Float :=
  distance seg.end1 seg.end2

def pt1 : Point := { x := 1.0, y := 2.0 }
def pt2 : Point := { x := 5.0, y := -1.0 }

def segment1 : Segment := { end1 := pt1, end2 := pt2 }

#eval length segment1
--  5.0000

-- names introduced by RectangularPrism.
#check RectangularPrism.height
#check RectangularPrism.width
#check RectangularPrism.depth
#check RectangularPrism
#check RectangularPrism.mk

--  What are tne names and type introduced by these structures?
structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Hamster         --  : Hamster : Type
#check Hamster.mk      --  : Hamster.mk (name : String) (fluffy : Bool) : Hamster
#check Hamster.name    --  : String
#check Hamster.fluffy  --  : Bool

#check Book         --  : Book : Type
#check Book.makeBook -- Book.makeBook (title author : String) (price : Float) : Book
#check Book.title   --  : String
#check Book.author  --  : String
#check Book.price   --  : Float


-- 1.6.5. Exercises - Polymorphism

--  Write a function to find the last entry in a list. It should return an `Option`.
def lastEntry {α : Type} (xs : List α) : Option α :=
  match xs with
  | []      => none
  | x :: [] => some x
  | _ :: xs => lastEntry xs

#eval lastEntry ([] : List Nat)  -- none
#eval lastEntry ['a']            -- some 'a'
#eval lastEntry [1, 2, 3]        -- some 3


-- Write a function that finds the first entry in a list that satisfies a given predicate.

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | []      => none
  | y :: ys =>
    match predicate y with
    | true  => some y
    | false => List.findFirst? ys predicate

#eval List.findFirst? [] (fun n => n = 3)       --  none
#eval List.findFirst? [3] (fun x => x = 3)      --  some 3
#eval List.findFirst? [1,2,3] (fun x => x = 3)  --  some 3
#eval List.findFirst? [3,2,1] (fun x => x = 3)  --  some 3
#eval List.findFirst? [1,2,3] (fun x => x = 4)  --  none
#eval List.findFirst? [1,3,2,3] (fun x => x = 3)  --  some 3


-- Write a function Prod.switch that switches the two fields in a pair for each other.
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#eval Prod.switch ('α', 'β')  --   ('β', 'α')


--  Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.
inductive PetName'
  | catName : String -> PetName'
  | dogName : String -> PetName'

def animals' : List PetName' :=
  [ PetName'.dogName "Spot",
    PetName'.catName "Tiger",
    PetName'.dogName "Fifi",
    PetName'.dogName "Rex",
    PetName'.catName "Floof"]

--  Pattern matching can be used to distinguish between the two constructors.
def PetName'.howManyDogs (pets : List PetName') : Nat :=
  match pets with
  | []  => 0
  | PetName'.catName _ :: morePets => howManyDogs morePets
  | PetName'.dogName _ :: morePets => howManyDogs morePets + 1

#eval PetName'.howManyDogs animals'  --  3


--  Write a function zip that combines two lists into a list of pairs.
--  The resulting list should be as long as the shortest input list.
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | []  => []
  | x :: xs =>
    match ys with
    | []  => []
    | y :: ys  => (x, y) :: zip xs ys

#eval zip ([] : List Nat) ([] : List Nat)   -- []
#eval zip [1,2,3] ['5','6','7']      --  [(1, '5'), (2, '6'), (3, '7')]
#eval zip [1,2,3] ['5','6','7','8']  --  [(1, '5'), (2, '6'), (3, '7')]
#eval zip [1,2,3,4] ['5','6','7']    --  [(1, '5'), (2, '6'), (3, '7')]


--  Write a polymorphic function take that returns the first n entries in a list, where n is a Nat.
--  If the list contains fewer than n entries, then the resulting list should be the entire input list.

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _  => []
  | _, [] => []
  | n, x :: xs => x :: take (n - 1) xs

#eval take 3 ["bolete", "oyster"]  --  ["bolete", "oyster"]
#eval take 2 ["bolete", "oyster"]  --  ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]  --  [ "bolete" ]
#eval take 0 ["bolete", "oyster"]  --  []
#eval take 1 ([] : List String)    --  []


-- Using the anlogy between types and arithmatic, write a function that distributes producs over
-- sums. In other words, it should have type `α × (β⊕γ) → (α × β) ⊕ (α × γ)`

def distribute {α β χ : Type} (v : (α × (β ⊕ χ))) : ((α × β) ⊕ (α × χ)) :=
  match v.snd with
  | Sum.inl n => Sum.inl (v.fst, n)
  | Sum.inr o => Sum.inr (v.fst, o)
