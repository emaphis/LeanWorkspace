--  1.4 Structures

--  Floating point type

#check 1.2  --  : Float

#check -454.2123215  --  : Float

#check 0.0  --  : Float

#check 0  -- : Nat

#check (0 : Float) --  : Float


--  A Cartesian point

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

#eval origin.x  -- 0.000000
#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
--  { x := -6.500000, y := 32.200000 }

def distance (p1 : Point) (p2 : Point) : Float :=
   Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
--  5.000000

--  Structures may share th same data components.

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

--  Type must be specified
--#check { x := 0.0, y := 0.0 }
--  invalid {...} notation, expected type is not known

#check ({ x := 0.0, y := 0.0 } : Point)  --  : Point


--  1.4.1. Updating Structures

--  Returns a new point.
def zeroX' (p : Point) : Point :=
  { x := 0, y := p.y }

def zeroX (p : Point) : Point :=
  { p with x := 0}

--  Given a point ..

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval fourAndThree
--  { x := 4.300000, y := 3.400000 }

#eval zeroX fourAndThree
--  { x := 0.000000, y := 3.400000 }

#eval fourAndThree
--   x := 4.300000, y := 3.400000 } - original value


--  1.4.2. Behind the Scenes

--  constructor
#check Point.mk 1.5 2.8
--  { x := 1.5, y := 2.8 } : Point

#check (Point.mk)
--  Point -> Point -> Point

--  accessor function

#check (Point.x)
--  Point.x : Point → Float

#check (Point.y)
--  Point.y : Point → Float
