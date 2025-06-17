import Feline

def bufsize : USize := 20 * 1024

/--
 The main work of feline is done by dump, which reads input one block
 at a time, dumping the result to standard output, until the end of
 the input has been reached. The end of the input is indicated by
 read returning an empty byte array:
-/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf <- stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout <- IO.getStdout
    stdout.write buf
    dump stream

/--
Open files that are provided as command-line arguments and emit
 their contents. When its argument is the name of a file that exists,
 `fileStream` returns a stream that reads the file's contents. When
  the argument is not a file, `fileStreamemits` an error and returns
  none.
-/
def fileStream (filename : System.FilePath) :IO (Option IO.FS.Stream) := do
  let fileExists <- filename.pathExists
  if not fileExists then
    let stderr <- IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle <- IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

/--
The main loop of feline is another tail-recursive function,
-/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin <- IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream <- fileStream (filename)
    match stream with
    | none => process 1 args
    | some stream =>
      dump stream
      process exitCode args


def main (args : List String) : IO UInt32 :=
  match args with
  | []  => process 0 ["-"]
  | _   => process 0 args
