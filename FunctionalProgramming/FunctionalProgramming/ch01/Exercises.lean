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

--  What are tne names and type introduced by these structures?
structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Hamster.name    --  : String
#check Hamster.fluffy  --  : Bool

#check Book.title   --  : String
#check Book.author  --  : String
#check Book.price   --  : Float
