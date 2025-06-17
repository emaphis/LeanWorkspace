# 2.4. Worked Example: cat

Write a simplified example of the Unix `cat` untility.

The standard Unix utility cat takes a number of command-line options, followed by zero or more input files. If no files are provided, or if one of them is a dash (-), then it takes the standard input as the corresponding input instead of reading a file. The contents of the inputs are written, one after the other, to the standard output. If a specified input file does not exist, this is noted on standard error, but cat continues concatenating the remaining inputs. A non-zero exit code is returned if any of the input files do not exist.

We will call it `feline`, lol.

## 2.4.1. Getting started

Create a new package project:

```shell
> lake new feline.
```

We will put all of our code in `Main.lean`

To compile run

```shell
> lake build
```

## 2.4.2. Concatenating Streams

Buffer size:

```Lean
def bufsize : USize := 20 * 1024
```

### 2.4.2.1. Streams

The main work of feline is done by dump, which reads input one block at a time, dumping the result to standard output, until the end of the input has been reached. The end of the input is indicated by read returning an empty byte array:

```Lean
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

IO.FS.Stream:

```Lean
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
```

Open files that are provided as command-line arguments and emit their contents. When its argument is the name of a file that exists, `fileStream` returns a stream that reads the file's contents. When the argument is not a file, `fileStreamemits` an error and returns none.

```Lean
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

### 2.4.2.2. Handling Input

The main loop of feline is another tail-recursive function,

```Lean
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args
```

### 2.4.2.3. Main

Main can have one of three forms

```Lean
main : IO Unit := ... --   corresponds to programs that cannot read their
                      --   command-line arguments and always indicate success
                      ---  with an exit code of 0,
```

```Lean
main : IO UInt32 := ...  --  corresponds to int main(void) in C, for programs
                         --  without arguments that return exit codes
```

```Lean
main : List String → IO UInt32   -- corresponds to `int main(int argc, char **argv)` in C,
                                 -- for programs that take arguments and signal success or failure.
```

If no arguments were provided, feline should read from standard input as if it were called with a single "-" argument. Otherwise, the arguments should be processed one after the other.

```Lean
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
```

### 2.4.3. Meow

```shell
*> echo "It works!" | lake exe feline
It works!
```

```shell
*feline> lake exe feline test1.txt test2.txt
It's time to find a warm spot and curl up!
```

```shell
*feline> echo "and purr" | lake exe feline test1.txt - test2.txt
It's time to find a warm spot"and purr"
 and curl up!
```
