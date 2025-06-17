--  2.1. Running a Program

--  Program:

def main : IO Unit := IO.println "Hello, world!"

-- Can be run from the console as

/-
> lean --run Hello.lean

Hello, world!

See: Hello.lean
-/

--  2.1.1. Anatomy of a Greeting

--  main should have an `IO Unit` declaration. Main is not a function because
--  it doesn't have -> in it's type.  It doesn't take parameters.

-- Programs of type `IO α` either return an exception or an `α`

#check IO.println  --  Function from String to IO actions
--   {α : Type u_1} → [inst : ToString α] → α → IO Unit

--  2.1.2. Functional Programming vs Effects

--  IO type is kinda like the world.
--  IO programs return a data structure of io effects that the lean Run Time System
--  interprets and executes


--  2.1.3. Real-World Functional Programming
--  In reality the IO 'world' is simply a token that gets 'updated' by an IO function.
--  If several IO actions are to be performed `do` notation can be used to sequence them.

--  2.1.4. Combining IO Actions.

--  HelloName.lean (see) sequences with `do` to read in and write out responces.

-- Combining IO actions
def main' : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input <- stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

/-
-- Execute with:
> lean --run HelloName.lean

FunctionalProgramming\ch02> lean --run HelloName.lean
How would you like to be addressed?
Edward
Hello, Edward!
-/

--  `<-` sshould be used in an IO action to create a variable instead of `:=`


--  2.2.4. IO Actions as Values

--  takes an IO action as its argument, returning a new action that will execute
--  the argument action twice.
def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval twice (IO.println "shy")
--shy
--shy

--  Generalized for `n` number of times

def nTimes (action : IO Unit) : Nat -> IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

 #eval nTimes (IO.println "Hello") 3

--Hello
--Hello
--Hello

--   IO actions are first-class values means that they can be saved in data structures for later execution.

def countdown: Nat -> List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

--  This list contains six elements (one for each number, plus a "Blast off!"
--  action for zero):

#eval from5.length  --  6

--   takes a list of actions and constructs a single action that runs them all in order:

def runActions : List (IO Unit) -> IO Unit
  | []  => pure ()
  | act :: actions => do
    act
    runActions actions

--  see runActions.lean

/-
*FunctionalProgramming\ch02> lean --run runActions.lean
5
4
3
2
1
Blast off!
-/


--  2.2.5. Exercise
--  Step through the execution of the following program on a piece of paper:

def main'' : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting

/-
--  See englishGreeting.lean

*FunctionalProgramming\ch02>lean --run englishGreeting.lean
Bonjour!
Hello!
-/
