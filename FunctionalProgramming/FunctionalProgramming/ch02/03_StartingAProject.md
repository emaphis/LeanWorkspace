# 2.3. Starting a Project

Lean is capable of producing complex multi-file programs with libraries.

`lake` - the Lean make tool

Lake is configuredd using a TOML file.

## 2.3.1. First steps

Create a new project

> lake new greeting

info: Version 4.1.2 of elan is available! Use `elan self update` to update.
info: downloading <https://releases.lean-lang.org/lean4/v4.20.1/lean-4.20.0-windows.tar.zst>
346.4 MiB / 346.4 MiB (100 %)  14.0 MiB/s ETA:   0 s
info: installing C:\Users\emaph\.elan\toolchains\leanprover--lean4---v4.20.1

c:\src\LeanWorkspace>

This creates a new Lean project in the `greeting` folder

With new files:

* Main.lean - is the file in which the Lean compiler will look for the main action.

* Greeting.lean - and Greeting/Basic.lean are the scaffolding of a support library for the program.

* lakefile.toml - contains the configuration that lake needs to build the application.

* lean-toolchain - contains an identifier for the specific version of Lean that is used for the project.

* Greeting/Basic.lean  - as a starter library file

```lean
def hello := "world"
```

* Greeting.lean  - Library file

```Lean
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

* Main.lean  - the starter Main file

```Lean
import Greeting
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

To build :

> lake build

To run:

> ./.lake/build/bin/greeting
Hello, world!

Or

>lake exe greeting

## 2.3.2. Lakefiles

* lakefile.toml

```toml
name = "greeting"
version = "0.1.0"
defaultTargets = ["greeting"]

[[lean_lib]]
name = "Greeting"

[[lean_exe]]
name = "greeting"
root = "Main"
```

This creates sections

* package settings, at the top of the file,

* a library declaration, named Greeting, and

* an executable, named greeting.

## 2.3.3. Libraries and Imports

Add Greeting/Smile.lean

```lean
def Expression.happy : String := "a big smile"
```

Updated Main.lean

```lean
import Greeting
import Greeting.Smile
open Expression
def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```

e\greeting>lake exe greeting
Hello, world, with a big smile!
