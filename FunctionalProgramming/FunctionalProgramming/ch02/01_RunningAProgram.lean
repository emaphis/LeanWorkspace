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
