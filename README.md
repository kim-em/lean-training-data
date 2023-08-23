# Data extraction from Lean libraries

This repository provides some tools for extracting data from Lean libraries (particularly Mathlib).
Most of the focus is data which may be useful for training ML models.
If you're looking for Lean training data and these tools don't give you what you want, please ask!
We would like to enable sharing of data and easy access to the Lean libraries for everyone.

## Tools

`declaration_types`
: For each declaration imported in the target file (e.g. `Mathlib`),
  print the name and type of the declaration.

`premises`
: For each declaration imported in a target file (e.g. `Mathlib`),
  list all of its direct dependencies (i.e. constants referenced from its type or proof).
  Constants appearing in explicit arguments are prefixed `*`,
  and constants used by the simplifier are prefixed `s`.

`training_data`
: Export all goal / tactic pairs from the library, with additional context.
  `--proofstep` outputs in `[GOAL]...[PROOFSTEP]...` format.

`tactic_benchmark`
: Run a tactic against every declaration in the library, tracking runtimes and successes.

`export_infotree`
: Export the `InfoTree` for each module as JSON.
  Filtering flags: `--tactics` (only tactic nodes) `--substantive` (no structuring tactics) and
  `--original` (no synthetic syntax nodes, e.g. from macro expansions)

## Usage instructions

* `git clone https://github.com/semorrison/lean-training-data.git`

* Install [`elan`](https://github.com/leanprover/elan) by running

```shell
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

* Go into the `lean-training-data` directory.
* Run `lake exe cache get` (this downloads precompiled binaries for `Mathlib`).
* Run `lake exe <tool>`, where `<tool>` is one of the programs documented below.

## Detailed instructions

### `declaration_types`

`lake exe declaration_types Mathlib` will import `Mathlib`, and then print the names and types
of every declaration in the environment.

Sample output:

```lean
---
theorem
TopologicalSpace.OpenNhds.map_id_obj
∀ {X : TopCat} (x : ↑X) (U : TopologicalSpace.OpenNhds (↑(CategoryTheory.CategoryStruct.id X) x)),
  (TopologicalSpace.OpenNhds.map (CategoryTheory.CategoryStruct.id X) x).obj U = U
```

The first line is the declaration type (`theorem`, `definition`, `inductive`, etc), the second line
is the name, and subsequent lines are the type. Each block is separated by `---`.

This takes about 16 minutes on my system (probably parallelizes if needed?)
producing a 45mb file, containing the types for ~190000 declarations in Mathlib/Std/Aesop/Qq/Cli.

### `premises`

`lake exe premises Mathlib` will calculate declaration dependencies up to a target file
(defaulting to all of Mathlib).

* Declarations are separated by `---`.
* In each block the first declaration is the theorem or definition we are analyzing,
* Subsequent indented declarations are those used in its proof or definition.
* Declarations prefixed with a `*` appear in explicit arguments.
  (This approximates "is visible in the pretty printed form".)
* Declarations prefixed with a `s` are used by the simplifier.

Sample output:

```lean
---
List.toFinset.ext_iff
* congrArg
  List.instMembershipList
  Finset
  Finset.instMembershipFinset
* Membership.mem
  List.toFinset
* iff_self
  List
* Iff
* congrFun
* congr
  True
* of_eq_true
  Eq
* Eq.trans
  DecidableEq
* forall_congr
s List.mem_toFinset
s Finset.ext_iff
s propext
```

This takes about 4 minutes on my system, producing a 115mb file,
containing information for ~170000 declarations in Mathlib and Std.

### `training_data`

`lake exe export_infotree Mathlib.Logic.Hydra` will recompile the target module,
and output all the tactic invocations appearing in the file.

The default output is a verbose human/machine readable format described below,
or the `--proofstep` flag just gives `[GOAL]...[PROOFSTEP]...` output
as used for training some models.

TODO: Break out individual steps of `rw` and `simp_rw`, with intermediate goals.
This is easy to do, just needs some plumbing.

The output consists of blocks of the form:

```text
===
Mathlib.Logic.Hydra
---
61
---
theorem cutExpand_le_invImage_lex [DecidableEq α] [IsIrrefl α r] :
    CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ (· ≠ ·)) (· < ·)) toFinsupp := by

---
α : Type u_1
r : α → α → Prop
inst✝¹ : DecidableEq α
inst✝ : IsIrrefl α r
⊢ CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) ↑toFinsupp
---
64:2-64:27
---
rintro s t ⟨u, a, hr, he⟩
---
case intro.intro.intro
α : Type u_1
r : α → α → Prop
inst✝¹ : DecidableEq α
inst✝ : IsIrrefl α r
s t u : Multiset α
a : α
hr : ∀ (a' : α), a' ∈ u → r a' a
he : s + {a} = t + u
⊢ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) (↑toFinsupp) s t
---
```

Here:

* `Mathlib.Logic.Hydra` is the name of the module where this goal occurs.
* `61` is the number of lines before the declaration (i.e. the `theorem` statement is on line `62`.)
* `theorem ...` is the *partial* declaration, including a fragment of the tactic proof.
* Next is the goal state at that point.
  (Typically just one goal, as we don't report the goal states before structuring commands.)
  Note that there is no guarantee that truncating the file at this point will actually cause Lean
  to display this goal: the presence of earlier structuring commands could result in Lean showing
  an error message instead.
* `64:2-64:27` is the range of positions occupied by the tactic invocation in the original file.
  This allows us to look up this goal in a live Lean session, so we can try out alternative tactics.
* `rintro s t ⟨u, a, hr, he⟩` is the tactic used in the library.
* After that is the goal state after running the tactic.
  (Often multiple goals.)"

There is also `scripts/training_data.sh`, which will run in parallel over all of Mathlib,
recording results in `out/training_data/`.

### `tactic_benchmark`

`lake exe tactic_benchmark --aesop Mathlib.Topology.ContinuousFunction.Ordered`
will run `aesop` on the type of each
declaration in the target module, reporting success or failure,
and the runtime (in seconds and heartbeats).

Sample output:

```shell
% lake exe tactic_benchmark --aesop Mathlib.Topology.ContinuousFunction.Ordered
Mathlib.Topology.ContinuousFunction.Ordered 7 21
❌ ContinuousMap.abs (0.006912s) (111 heartbeats)
❌ ContinuousMap.instAbsContinuousMap (0.007926s) (115 heartbeats)
✅ ContinuousMap.abs_apply (0.027873s) (401 heartbeats)
❌ ContinuousMap.partialOrder (0.008932s) (105 heartbeats)
✅ ContinuousMap.le_def (0.071422s) (984 heartbeats)
❌ ContinuousMap.lt_def (0.162438s) (2284 heartbeats)
❌ ContinuousMap.sup (0.012593s) (118 heartbeats)
✅ ContinuousMap.sup_coe (0.204213s) (2838 heartbeats)
✅ ContinuousMap.sup_apply (0.201279s) (2799 heartbeats)
❌ ContinuousMap.semilatticeSup (0.007805s) (119 heartbeats)
❌ ContinuousMap.inf (0.010117s) (119 heartbeats)
✅ ContinuousMap.inf_coe (0.175238s) (2798 heartbeats)
✅ ContinuousMap.inf_apply (0.174505s) (2683 heartbeats)
❌ ContinuousMap.semilatticeInf (0.007189s) (119 heartbeats)
❌ ContinuousMap.instLatticeContinuousMap (0.007780s) (119 heartbeats)
❌ ContinuousMap.sup'_apply (0.049451s) (727 heartbeats)
❌ ContinuousMap.sup'_coe (0.069892s) (1101 heartbeats)
❌ ContinuousMap.inf'_apply (0.049896s) (728 heartbeats)
❌ ContinuousMap.inf'_coe (0.070128s) (1102 heartbeats)
❌ ContinuousMap.IccExtend (0.030286s) (466 heartbeats)
✅ ContinuousMap.coe_IccExtend (0.148204s) (2390 heartbeats)
```

Currently supported flags are `--aesop`, `--simp_all` (which runs `intros; simp_all`),
`--rfl` (which runs `intros; rfl`), and `--exact` (which runs `exact?`),
but it is trivial to add more by editing `tactic_benchmark.lean`.

There is also `scripts/tactic_benchmark.sh`, which will run in parallel over all of Mathlib,
recording results in `out/tactic_benchmark/`.

After you've run it, `scripts/tactic_benchmark_summary.sh` will report the success rates,
as well as the differential success rates
(e.g. number of goals solved by `simp_all` but not by `aesop`).

TODO: run on all tactic goals in the library, not just the types of declarations.
Should not be difficult given the existing components.

### `export_infotree`

`lake exe export_infotree Mathlib.Logic.Hydra` will recompile the target module,
extract the `InfoTree`s, and then write these out as JSON to stdout.
The JSON contains pretty-printed goals before and after every tactic invocation,
and the pretty-printed syntax of every tactic invocation, and explicitly constructed term.

There is also `scripts/export_infotree.sh`, which will run in parallel over all of Mathlib,
recording results in `out/export_infotree/`.

If you need to use this tool,
consider modifying one of the other tools to give you directly what you want!

## See also

### LeanDojo

[LeanDojo](https://leandojo.org/) provides similar tools.

I like that the tools provided here are standalone tools provided separately from any model or benchmark.
They are "pure lean" (plus a little bash scripting), and may be useful models for anyone interested
in metaprogramming tools for examining compiled Lean code.

### Releases

You can find a downloadable copy of the output of all these tools under `Releases`.
Please ping me if you'd like these to be updated. (We could run a CI job.)

### Derivatives

If you use these tools or the downloadable releases to prepare other publicly available datasets
(e.g. train/test splits) or models, please reference this repository to help others find it.
