--  runActions.lean  - example from 2.2.4. IO Actions as Values

--   IO actions are first-class values means that they can be saved in data structures for later execution.

def countdown: Nat -> List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

--  This list contains six elements (one for each number, plus a "Blast off!"
--  action for zero):

--#eval from5.length  --  6

--   takes a list of actions and constructs a single action that runs them all in order:

def runActions : List (IO Unit) -> IO Unit
  | []  => pure ()
  | act :: actions => do
    act
    runActions actions

def main : IO Unit := runActions from5
