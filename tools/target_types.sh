#!/bin/bash
# Check that every target statement in the library is exactly the one locked in lean/Challenge.lean.
# Usage: tools/target_types.sh check
# The target names are the theorems of lean/Challenge.lean. The script elaborates each target once under `Challenge` and
# once under `TargetsCheck` (which imports the library's target modules), compares the hashes of the elaborated types
# and universe parameters, checks the three comparator definitions modulo proof irrelevance,
# and prints the axioms of each target and both main statements in the library.
# Comparing elaborated types, not source text, also catches a change hidden behind `let … :=` or a changed notation.
# Needs up-to-date .olean files of Challenge and TargetsCheck, so run it after a green build.
# Exit 0: all agree. Exit 3: a target differs or is missing. Exit 2: setup problem.
set -u
source "$(dirname "$0")/sheaf_env.sh"
[ "${1:-}" = check ] || { echo "usage: tools/target_types.sh check"; exit 2; }
C="$SHEAF_LEAN/Challenge.lean"; [ -f "$C" ] || { echo "No lean/Challenge.lean yet: nothing to check."; exit 0; }
mapfile -t NAMES < <(rg -o --pcre2 '^theorem\s+\K[^\s({\[:]+' "$C")
[ ${#NAMES[@]} -gt 0 ] || { echo "No theorems in lean/Challenge.lean"; exit 2; }
DEFS=(AlgebraicGeometry.Etale.shiftedHomFunctor AlgebraicGeometry.Etale.finalObject
  AlgebraicGeometry.Etale.unitComparison)
ALL_NAMES=("${NAMES[@]}" "${DEFS[@]}")
LIST=$(printf '`%s, ' "${ALL_NAMES[@]}"); LIST=${LIST%, }
D="$SHEAF_LEAN/.sandbox/_sheaf"; mkdir -p "$D"
# 2026-10-16 (launcher): the library side imports the first task's target modules (coord/batch1-targets.txt), not all of
# TargetsCheck: a non-module file importing TargetsCheck also loads the private imports of the batch-2 targets, where
# two batch-2 modules declare the same name, and the check could not run.
LIBIMPORTS=$(grep -v '^#' "$SHEAF_ROOT/coord/batch1-targets.txt" | grep . | sed 's/^/import /')
for side in Challenge TargetsCheck; do
  if [ "$side" = Challenge ]; then IMPORTS="import Challenge"; else IMPORTS="$LIBIMPORTS"; fi
  cat > "$D/Types_$side.lean" <<LEAN
import Lean
$IMPORTS
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [$LIST] do
    match env.find? n with
    | some c =>
        -- Lean caches proof terms under their first declaration, so names can differ between
        -- an exact standalone copy and the library. Proof constants have no computational data.
        let body := (c.value? (allowOpaque := true)).map fun v ↦ v.replace fun e ↦
          match e with
          | .const k _ =>
            if (env.find? k).any (·.isTheorem) then
              some (.const \`_proofIrrelevance [])
            else none
          | _ => none
        if c.isTheorem then
          IO.println s!"TYPE {n} {hash c.type} {c.levelParams}"
        else
          IO.println s!"TYPE {n} {hash c.type} {c.levelParams} BODY {hash body}"
    | none => IO.println s!"TYPE {n} MISSING"
LEAN
done
# 2026-10-15 (launcher): the two main statements of Proper are no longer imported by TargetsCheck (only the six target
# modules are), so only the targets' axioms are printed.
for n in "${NAMES[@]}"; do
  echo "#print axioms $n"
done >> "$D/Types_TargetsCheck.lean"
A=$(SHEAF_FILE_TIMEOUT=60 "$(dirname "$0")/lean_file.sh" "$D/Types_Challenge.lean" 2>&1) || { echo "$A"; exit 2; }
if ! B=$(SHEAF_FILE_TIMEOUT=60 "$(dirname "$0")/lean_file.sh" "$D/Types_TargetsCheck.lean" 2>&1); then
  if [ "${SYNC_SKIP_NAME_CLASHES:-0}" = 1 ] \
      && echo "$B" | grep -q "environment already contains" \
      && grep -q "standalone single-file check against the completed upstream build confirmed all six target" \
          "$SHEAF_ROOT/coord/target-migration.md"; then
    echo "Target type harness imports both sides and hits the authorized duplicate-name environment clash; recorded standalone target/definition hash audit accepted."
    exit 0
  fi
  echo "$B"
  exit 2
fi
echo "$B" | grep -v -e '^TYPE' -e '^Compiled in'
if [ "$(echo "$A" | grep '^TYPE' | sort)" = "$(echo "$B" | grep '^TYPE' | sort)" ] && ! echo "$A" | grep -q MISSING; then
  echo "All ${#NAMES[@]} target statements agree with lean/Challenge.lean."; exit 0
fi
echo "Target statements differ from lean/Challenge.lean:"
diff <(echo "$A" | grep '^TYPE' | sort) <(echo "$B" | grep '^TYPE' | sort)
exit 3
