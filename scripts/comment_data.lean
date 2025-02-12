import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Data.String.Basic
import Cli

open Lean Elab IO Meta
open Cli System

structure CommentData where
  declName : String
  declType : String
  docString : Option String
  context : String
  decl : String
deriving ToJson, FromJson

def addStep (data : String × List CommentData) (step : CompilationStep) :
    IO (String × List CommentData) := do
  let (context, prev) := data
  let decl := step.src.toString
  let context := context ++ decl
  let new ← step.newDecls
  let next := new.map fun d =>
  { context
    docString := d.docString
    declName := d.name.toString
    declType := d.ppType
    decl }
  return (context, next ++ prev)

def commentData (args : Cli.Parsed) : IO UInt32 := do
    initSearchPath (← findSysroot)
    let module := args.positionalArg! "module" |>.as! ModuleName
    let steps ← compileModule module
    let (_, data) ← steps.foldlM (init := ("", [])) addStep
    IO.println <| toJson data
    return 0

/-- Setting up command line options and help text for `lake exe comment_data`. -/
def comment_data : Cmd := `[Cli|
  comment_data VIA commentData; ["0.0.1"]
"Export doc-string training data from the given file.

The output is a json array of dictionaries with fields
* `declName`: the declaration name
* `declType`: the pretty-printed type of the declaration
* `docString`: the declaration doc-string, if it is present
* `decl`: the entire body of the declaration
* `context`: the file source up to before the declaration
  (this currently does not include the imports)
"

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe comment_data` -/
def main (args : List String) : IO UInt32 :=
  comment_data.validate args

-- See `scripts/comment_data.sh` for a script to run this on all of Mathlib.
