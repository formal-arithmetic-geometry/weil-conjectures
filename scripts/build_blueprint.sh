#!/usr/bin/env bash
# Build and render the Verso blueprint to _out/site/html-multi/.
#
# This is a thin replacement for `lake exe vbp build`, which currently fails on
# this repository because it assumes the Lake package name (`weil-conjectures`)
# is also a buildable module name. We run the same stages by hand: build the
# Blueprint library, then run the generator entry point through Lake's Lean
# wrapper.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Blueprint
lake lean blueprint/BlueprintMain.lean -- --run blueprint/BlueprintMain.lean \
  --output _out/site "$@"

echo
echo "Blueprint site written to _out/site/html-multi/"
echo "Preview with:  python3 -m http.server 8000 -d _out/site/html-multi"
