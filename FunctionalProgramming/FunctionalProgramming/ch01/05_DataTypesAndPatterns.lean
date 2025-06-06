--  1.5. Datatypes and Patterns

--  1.5.1. Pattern Matching

inductive Bool' where
  | false : Bool'
  | true  : Bool'


inductive Nat' where
  | zero' : Nat'
  | succ' (n : Nat') : Nat'


--  1.5.1. Pattern Matching

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero Nat.zero  --  true
#eval isZero (Nat.succ Nat.zero)  --  false

#eval Nat.succ Nat.zero  --  1

#eval isZero 5  --  false

def five : Nat :=  (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
#eval five  -- 5
#eval isZero five  -- false

#eval Nat.pred 5  --  4
#eval Nat.pred 0  --  0


def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5  --  4
#eval pred 0  --  0


--  1.5.2. Recursive Functions

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

-- Lean will prove that a recursive function will end.
--def evenLoops (n : Nat) : Bool :=
--  match n with
--  | Nat.zero => true
--  | Nat.succ k => not (evenLoops n)


def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

#eval plus 3 2  --  5


def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')


-- Lean detects tha prameter may not terminate
--def div' (n : Nat) (k : Nat) :=
--  if n < k then 0
--  else Nat.succ (div' (n - k) k)
