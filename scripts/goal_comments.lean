import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Mathlib.Tactic.Change
import Cli

open Lean Elab IO Meta
open Cli System

instance : LE Position where
  le p₁ p₂ := p₁.line < p₂.line ∨ p₁.line = p₂.line ∧ p₁.column ≤ p₂.column

instance : DecidableRel ((· : Position) ≤ ·) := by
  change DecidableRel fun _ _ => _ ∨ _
  infer_instance

def Range := Position × Position
deriving DecidableEq, Repr, ToString

instance : LE Range where
  le r₁ r₂ := r₂.1 ≤ r₁.1 ∧ r₁.2 ≤ r₂.2

instance : LT Range where
  lt r₁ r₂ := r₁ ≤ r₂ ∧ r₁ ≠ r₂

instance : DecidableRel ((· : Range) ≤ ·) := by
  change DecidableRel fun _ _ => _ ∧ _
  infer_instance

instance : DecidableRel ((· : Range) < ·) := by
  change DecidableRel fun _ _ => _ ∧ _
  infer_instance

namespace Lean.Elab.TacticInvocation

def rangesAndGoals (i : TacticInvocation) : IO (Range × String) := do
  return ⟨i.range, (Format.joinSep (← i.goalStateAfter) "\n").pretty 1000000⟩

end Lean.Elab.TacticInvocation

partial def dropEnclosed (L : List (Range × String)) : List (Range × String) :=
  let L' := L.filter fun ⟨r, _⟩ => ¬ L.any fun ⟨r', _⟩ => r < r'
  if L' = L then L' else dropEnclosed L'

example : True := by trivial

def justTheGoal (s : String) : String :=
  if s = "" then "🎉 no goals" else
  let lines := s.splitOn "\n"
  let goals := lines.filter fun l => l.startsWith "⊢ "
  match goals with
  | [] => ""
  | [g] => if g.length > 80 then
      g.take 78 ++ " …"
    else
      g
  | _ => ""

def String.indent (s : String) (k : Nat) : String := ⟨List.replicate k ' '⟩ ++ s

def goalComments (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compile_time_search_path%
    let module := args.positionalArg! "module" |>.as! ModuleName
    let mut trees ← moduleInfoTrees module
    trees := trees.bind InfoTree.retainTacticInfo
    trees := trees.bind InfoTree.retainOriginal
    trees := trees.bind InfoTree.retainSubstantive
    let L₁ ← (trees.bind InfoTree.tactics).mapM TacticInvocation.rangesAndGoals
    let L₂ := dropEnclosed L₁ |>.filter fun ⟨⟨⟨l₁, _⟩, ⟨l₂, _⟩⟩, _⟩  => l₁ = l₂
    let L₃ := (L₂.map fun ⟨r, s⟩ => (r, justTheGoal s)) |>.filter fun ⟨_, s⟩ => s != ""
    let mut src := (← moduleSource module).splitOn "\n"
    for ⟨⟨⟨l, c⟩, _⟩, s⟩ in L₃.reverse do
      let toInsert := ("-- " ++ s).indent c
      if src.get? l ≠ toInsert then
        src := src.insertNth l toInsert
    let out := ("\n".intercalate src)
    if args.hasFlag "edit" then
      IO.FS.writeFile (← findLean module) out
    IO.println out
    return 0

/-- Setting up command line options and help text for `lake exe goal_comments`. -/
def goal_comments : Cmd := `[Cli|
  goal_comments VIA goalComments; ["0.0.1"]
"Modify a Lean file by inserting comments after every tactic invocation showing the goal.
Prints the modified source code to stdout."

  FLAGS:
    "edit";      "Also edit the source code in place."

  ARGS:
    module : ModuleName; "Lean module to compile and annotate with goal comments."
]

/-- `lake exe goal_comments` -/
def main (args : List String) : IO UInt32 :=
  goal_comments.validate args

-- See `scripts/goal_comments.sh` for a script to run this on all of Mathlib.
