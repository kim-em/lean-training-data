#!/usr/bin/env bash

## Generates pretty-printed descriptions of every goal/tactic pair.

# See the help text in `lake exe training_data` for a description of the output format.

# Run either as `scripts/training_data.sh` to run on all of Mathlib (several hours),
# or `scripts/training_data.sh Mathlib.Logic.Hydra` to run on just one file.
# Results will go in `out/training_data/Mathlib.Logic.Hydra.train`.

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
  lake build training_data
  parallel -j32 ./scripts/training_data.sh ${FLAGS[@]} -- ::: `cat .lake/packages/mathlib/Mathlib.lean | sed -e 's/import //'`
else
  DIR=out/training_data
  mkdir -p $DIR
  mod=${ARGS[0]}
  if [ ! -f $DIR/$mod.train ]; then
    echo $mod
    if [ ! -f .lake/build/bin/training_data ]; then
      lake build training_data
    fi
    .lake/build/bin/training_data ${FLAGS[@]} $mod > $DIR/$mod._train && mv $DIR/$mod._train $DIR/$mod.train
  fi
fi
