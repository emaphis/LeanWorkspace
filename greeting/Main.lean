import Greeting.Basic
import Greeting.Smile  -- new file in library

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
