import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import Mathlib.Tactic.ToExpr -- Upstreamed to std4 as https://github.com/leanprover/std4/pull/221
import Mathlib.Lean.CoreM
import Std.Lean.Util.Path
import Cli

open Lean Elab IO Meta
open Cli System

structure InfoTreeExport where
  name : Name
  trees : List Json
deriving ToJson

def exportInfoTree (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compile_time_search_path%
    let target := args.positionalArg! "module" |>.as! ModuleName
    let mut trees ← moduleInfoTrees target
    if args.hasFlag "tactics" then
      trees := (trees.map InfoTree.retainTacticInfo).join
    if args.hasFlag "original" then
      trees := (trees.map InfoTree.retainOriginal).join
    if args.hasFlag "substantive" then
      trees := (trees.map InfoTree.retainSubstantive).join
    let json ← trees.mapM fun t => t.toJson none
    IO.println <| toJson <| InfoTreeExport.mk target json
    return 0

/-- Setting up command line options and help text for `lake exe export_infotree`. -/
def export_infotree : Cmd := `[Cli|
  export_infotree VIA exportInfoTree; ["0.0.1"]
  "Export the InfoTrees for a file as JSON."

  FLAGS:
    "tactics";      "Only export TacticInfo nodes."
    "original";     "Skip nodes with synthetic syntax."
    "substantive";  "Skip tactic combinators."

  ARGS:
    module : ModuleName; "Lean module to compile and export InfoTrees."
]

/-- `lake exe export_infotree` -/
def main (args : List String) : IO UInt32 :=
  export_infotree.validate args

-- See `./scripts/export_infotree.sh` to run this against all of Mathlib.
