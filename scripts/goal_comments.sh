#!/usr/bin/env bash

## Updates the source code of a module to contain `-- ⊢ ...` comments after every tactic.

# Run either as `scripts/goal_comments.sh --edit` to run on all of Mathlib (several hours),
# or `scripts/goal_comments.sh Mathlib.Logic.Hydra` to run on just one file.
# Results will be written back out to the copy of Mathlib in `lake-packages/mathlib/`.
# This script is not idempotent, so you may need to clean up that copy before running again.

FLAGS=()
ARGS=()

for arg in "$@"; do
    if [[ $arg == --* ]]; then
        FLAGS+=("$arg")
    else
        ARGS+=("$arg")
    fi
done

if [ ${#ARGS[@]} -eq 0 ]; then
  rm -f ./build/lake.lock
  lake build training_data
  parallel -j32 ./scripts/goal_comments.sh ${FLAGS[@]} -- ::: `cat lake-packages/mathlib/Mathlib.lean | sed -e 's/import //'`
else
  DIR=out/goal_comments
  mkdir -p $DIR
  mod=${ARGS[0]}
  if [ ! -f $DIR/$mod.lean ]; then
    echo $mod
    if [ ! -f build/bin/goal_comments ]; then
      lake build goal_comments
    fi
    build/bin/goal_comments ${FLAGS[@]} $mod > $DIR/$mod._lean && mv $DIR/$mod._lean $DIR/$mod.lean
  fi
fi
