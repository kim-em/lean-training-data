import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Std.Lean.HashMap
import Std.Lean.Util.Path

/-!
Generate declaration dependencies up to a target file (defaulting to all of Mathlib).

* Declarations are separated by `---`.
* In each block the first declaration is the theorem or definition we are analyzing,
* Subsequent indented declarations are those used in its proof or definition.
* Declarations prefixed with a `* ` appear in explicit arguments.
  (This approximates "is visible in the pretty printed form".)
* Declarations prefixed with a `s ` are used by the simplifier.

-/

open Lean Meta

def isAuxLemma : Name → Bool
| .num (.str _ "_auxLemma") _ => true
| _ => false

partial def Lean.ConstantInfo.getUsedConstants' (c : ConstantInfo)
    (constantsMap : HashMap Name ConstantInfo)
    (unfolding : Name → Bool := isAuxLemma) : NameSet × NameSet := Id.run do
  let mut direct : NameSet := ∅
  let mut unfolded : NameSet := ∅
  for n in c.getUsedConstantsAsSet do
    if unfolding n then
      if let some c := constantsMap.find? n then
        unfolded := unfolded ++ c.getUsedConstantsAsSet
    else
      direct := direct.insert n
  return (direct, unfolded)

/--
Traverse all constants from imported files,
collecting the constants which are used in either the type or value of the theorem or definition.

A predicate `unfolding` picks out a class of constants which should not be returned,
but instead replaced with the set of constants appearing in their type or value.
The typical use case is to unfold `_auxLemma`s generated dynamically by the simplifier.
-/
def allUsedConstants (unfolding : Name → Bool := isAuxLemma) :
    CoreM (NameMap (NameSet × NameSet)) := do
  let constantsMap := (← getEnv).constants.map₁
  let mut result : NameMap (NameSet × NameSet) := ∅
  for (n, c) in constantsMap do
    -- We omit all internally generated auxiliary statements.
    if ! (← n.isBlackListed) then
      result := result.insert n (c.getUsedConstants' constantsMap unfolding)
  return result

open Lean in
elab "#printNum " n:ident i:num : command => do
  let name := Name.num n.getId i.getNat
  let some decl := (← getEnv).find? name | throwError "no such declaration {name}"
  logInfo m!"{name} : {decl.type} :=\n{decl.value?.getD (.bvar 0)}"

/--
Traverse an expression, collecting `Name`s,
but do not descend into implicit arguments.
-/
partial def Lean.Expr.explicitConstants : Expr → MetaM NameSet
| .app f x => do
  -- We wrap with `try?` here because on tiny fraction of declarations in Mathlib,
  -- e.g. `Computation.exists_of_mem_parallel`, this fails with an error like
  -- `function expected ?m.88 ?m.93`.
  match (← try? (inferType f)) with
  | some (.forallE _ _ _ .default) => return (← f.explicitConstants) ++ (← x.explicitConstants)
  | _ => f.explicitConstants
| .lam _ t b _ => do b.instantiate1 (← mkFreshExprMVar t) |>.explicitConstants
| .forallE _ t b _ => do b.instantiate1 (← mkFreshExprMVar t) |>.explicitConstants
| .letE n t v b _ => return (← v.explicitConstants)
    ++ (← withLetDecl n t v fun fvar => (b.instantiate1 fvar).explicitConstants)
| .const n _ => return NameSet.empty.insert n
| .mdata _ e => e.explicitConstants
| _ => return NameSet.empty

/--
Collect all the constants used in the values of theorem or definition,
ignoring implicit arguments of functions.
-/
def Lean.ConstantInfo.explicitConstants (c : ConstantInfo) : MetaM NameSet := do
  match c.value? with
  | some e => e.explicitConstants
  | none => return ∅

/--
Traverse all constants from imported files,
collecting the constants which are used in the value of the theorem or definition,
ignoring implicit arguments of functions.
-/
def allExplicitConstants : MetaM (NameMap NameSet) := do
  let r := (← getEnv).constants.map₁
  let mut result : NameMap NameSet := ∅
  for (n, c) in r do
    -- We omit all internally generated auxiliary statements.
    if ! (← n.isBlackListed) then
      result := result.insert n (← c.explicitConstants)
  return result

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let allConstants ← allUsedConstants
    let explicitConstants ← MetaM.run' allExplicitConstants
    for (n, (d, u)) in allConstants do
      match n.components with
      -- Note we keep `Std` as it has many lemmas about numbers and data structures.
      | "Lean" :: _
      | "Qq" :: _
      | "Cli" :: _
      | "Aesop" :: _ => continue
      | components => if components.contains "Tactic" then continue
      let explicit := explicitConstants.find? n |>.getD ∅
      IO.println "---"
      IO.println n
      for m in d do
        if explicit.contains m then
          IO.println s!"* {m}"
        else
          IO.println s!"  {m}"
      for m in u do
        if ! d.contains m then
          IO.println s!"s {m}"
  return 0
