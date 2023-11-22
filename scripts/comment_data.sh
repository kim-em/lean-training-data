#!/usr/bin/env bash

## Extracts doc-strings for every declaration.

# See the help text in `lake exe comment_data` for a description of the output format.

# Run either as `scripts/comment_data.sh` to run on all of Mathlib (several hours),
# or `scripts/comment_data.sh Mathlib.Logic.Hydra` to run on just one file.
# Results will go in `out/comment_data/Mathlib.Logic.Hydra.comments`.

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
  lake build comment_data
  parallel -j32 ./scripts/comment_data.sh ${FLAGS[@]} -- ::: `cat .lake/packages/mathlib/Mathlib.lean | sed -e 's/import //'`
else
  DIR=out/comment_data
  mkdir -p $DIR
  mod=${ARGS[0]}
  if [ ! -f $DIR/$mod.comment ]; then
    echo $mod
    if [ ! -f .lake/build/bin/comment_data ]; then
      lake build comment_data
    fi
    .lake/build/bin/comment_data ${FLAGS[@]} $mod > $DIR/$mod._comment && mv $DIR/$mod._comment $DIR/$mod.comment
  fi
fi
