--  1.6. Polymorphism

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
 { x := Nat.zero, y := Nat.zero }

 #eval natOrigin
 --  { x := 0, y := 0 }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check replaceX
--  replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α

-- curring to produce a specifically typed `replaceX`
#check replaceX Nat
--  replaceX Nat : PPoint Nat → Nat → PPoint Nat

def replaceNat := replaceX Nat

#eval replaceNat natOrigin 5
--  { x := 5, y := 0 }


inductive Sign where
  | pos
  | net

--  A function whoere argument is a Sign
def posOrNegThree (s : Sign) :
    match s wiht | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos  => (3 : Nat)
  | Sign.net  => (-3 : Int)
