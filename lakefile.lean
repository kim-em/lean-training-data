import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib TrainingData where

@[default_target]
lean_lib Examples where

@[default_target]
lean_exe tactic_benchmark where
  root := `scripts.tactic_benchmark
  supportInterpreter := true

@[default_target]
lean_exe export_infotree where
  root := `scripts.export_infotree
  supportInterpreter := true

@[default_target]
lean_exe training_data where
  root := `scripts.training_data
  supportInterpreter := true

@[default_target]
lean_exe premises where
  root := `scripts.premises

@[default_target]
lean_exe declaration_types where
  root := `scripts.declaration_types

@[default_target]
lean_exe goal_comments where
  root := `scripts.goal_comments
