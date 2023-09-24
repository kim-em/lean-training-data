import TrainingData.Frontend
import Std.Lean.Util.Path
import Cli

open Lean Elab IO Meta
open Cli System

def verify (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compile_time_search_path%
    verifyModule (args.positionalArg! "module" |>.as! ModuleName)
    pure 0

/-- Setting up command line options and help text for `lake exe verify`. -/
def verifyCli : Cmd := `[Cli|
  verify VIA verify; ["0.0.1"]
"Verify an importable module, by replaying its declarations into the environment."

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe verify` -/
def main (args : List String) : IO UInt32 :=
  verifyCli.validate args
