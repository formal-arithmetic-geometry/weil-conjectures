#!/bin/bash
# Names that two modules of the library both declare, with different types, universe parameters or as definitions.
# Usage: tools/name_clashes.sh [all]      default: the modules the targets reach; `all`: the whole library
# The global build does not see such a pair while no file of Lean's module system imports both publicly; a file that
# is not of the module system and imports both (tools/target_types.sh, the comparator) fails with "environment already
# contains". The usual case is two anonymous instances of the same class: give one of them a name.
# Reads the compiled files of the last published build (tools/name_clashes.lean); elaborates nothing.
# Exit 0: none. Exit 1: clashes printed, one per line: the name, the modules, the kinds.
source "$(dirname "$0")/sheaf_env.sh"
L=$(mktemp); trap 'rm -f "$L"' EXIT
python3 - "$SHEAF_ROOT" "${1:-targets}" > "$L" <<'PY'
import sys
sys.path.insert(0, sys.argv[1] + "/tools")
import leanindex as li, queue
imports, dist = queue.analyse()
mods = imports if sys.argv[2] == "all" else dist
print("\n".join(sorted(m for m in mods if m.split(".")[0] in li.library_dirs() and "." in m)))
PY
OUT=$(cd "$SHEAF_LEAN" && SHEAF_CLASH_MODULES="$L" lake env lean "$SHEAF_ROOT/tools/name_clashes.lean" 2>&1)
echo "$OUT" | grep -v -e '^CLASH SAME-THM' -e '^NOOLEAN' | grep . && exit 1
echo "No name is declared twice with different content in $(grep -c . "$L") modules ($(echo "$OUT" | grep -c '^CLASH SAME-THM') helper lemmas generated identically in several modules, which Lean accepts)."
