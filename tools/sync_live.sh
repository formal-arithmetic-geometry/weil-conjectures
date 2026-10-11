#!/bin/bash
# Bring this side copy (branch stage3-prep, one-library layout) up to date with the live branch, in one command.
# Usage: tools/sync_live.sh [<live repository> [<branch or commit>]]     default: ~/weil-conjectures-sheaf sheaf-dag
# Only reads the live repository (git fetch from its path). In this copy it merges the live branch, keeps this copy's
# layout of lean/ (the adopted source library, lakefile, TargetsCheck, Challenge), takes lean/Sheaf whole from the live
# branch and converts it again with tools/to_module.py --live (module system, the private names used in exposed text,
# the repairs of tools/to_module_fixes.tsv), and commits. A conflict in coord/ or dag/ takes the live version; any other conflict outside lean/ stops it with the list, nothing
# committed (resolve, `git add`, run `tools/sync_live.sh --continue`). The live commit is recorded in
# coord/stage3-synced-with.txt, which ~/cc1/switch-stage3.sh compares with the live tip. Build afterwards:
#   cd lean && LEAN_NUM_THREADS=12 nice lake build Sheaf TargetsCheck SheafChallenge
set -euo pipefail
cd "$(dirname "$0")/.."
[ "$(git symbolic-ref --short HEAD)" = stage3-prep ] || { echo "not on branch stage3-prep"; exit 2; }
if [ "${1:-}" != --continue ]; then
  LIVE=${1:-$HOME/weil-conjectures-sheaf}; REV=${2:-sheaf-dag}
  [ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "uncommitted changes: commit them first"; exit 2; }
  git fetch -q "$LIVE" "$REV"
  NEW=$(git rev-parse FETCH_HEAD); echo "$NEW" > .git/STAGE3_SYNC
  git merge --no-commit --no-ff FETCH_HEAD > /dev/null 2>&1 || true
  # lean/: this copy's layout stays; lean/Sheaf is the live one, converted
  git checkout -q HEAD -- lean ':!lean/Sheaf' 2>/dev/null || true
  git rm -rq --cached --ignore-unmatch lean/Sheaf; rm -rf lean/Sheaf
  git checkout -q "$NEW" -- lean/Sheaf
  # coord/ and dag/ are the live repository's: a conflict there takes the live version (coord/sheaf.env stays ours)
  for f in $(git diff --name-only --diff-filter=U -- coord dag); do git checkout -q "$NEW" -- "$f" 2>/dev/null || git rm -q --cached "$f"; done
  git checkout -q HEAD -- coord/sheaf.env
fi
NEW=$(cat .git/STAGE3_SYNC)
python3 tools/to_module.py --live || { echo "to_module reported a problem (above): repair tools/to_module_fixes.tsv, then tools/sync_live.sh --continue"; exit 1; }
git add -A lean
U=$(git diff --name-only --diff-filter=U)
[ -z "$U" ] || { echo "conflicts, nothing committed:"; echo "$U"; exit 1; }
echo "$NEW" > coord/stage3-synced-with.txt; git add coord/stage3-synced-with.txt
git commit -q -m "stage3-prep: sync with live sheaf-dag $(git rev-parse --short=9 "$NEW") (lean/Sheaf converted by tools/to_module.py --live)"
echo "synced with $(git rev-parse --short=9 "$NEW"): $(find lean/Sheaf -name '*.lean' | wc -l) Sheaf modules; commit $(git rev-parse --short=9 HEAD)"
