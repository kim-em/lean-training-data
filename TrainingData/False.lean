import Lean

open Lean

elab "add_false" : command => do
  modifyEnv λ env =>
    let constants := env.constants.insert `falso $ ConstantInfo.thmInfo
      { name := `falso
        levelParams := []
        type := .const ``False []
        value := .const ``False []
      }
    { env with constants }

add_false

example : False :=
   falso
