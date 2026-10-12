#!/bin/bash
# Compile one Lean file of a remote group on this server (stages 2 and 3; decision of the human, 2026-10-11).
# Usage (over ssh, no SHEAF_LEAD needed):
#   ssh <server> 'cd ~/weil-conjectures-sheaf && tools/compile_remote.sh <group> <item>' < <file.lean>
#   tools/compile_remote.sh <group> <item> <path-of-an-uploaded-file.lean>
# <item> is a node id (stage 2) or a module name (stage 3), written with dots or with `_` for every dot:
# Sheaf.Paper.Foo and Sheaf_Paper_Foo both give lean/.sandbox/<group>/Sheaf_Paper_Foo.lean.
# The file is written to lean/.sandbox/<group>/<item>.lean and compiled with tools/lean_file.sh (time limit
# SHEAF_FILE_TIMEOUT, default 60 s) against the last green global build plus the group's own landings.
# Prints the compiler's messages and "Compiled in N s" or the errors; the exit code is lean's (124 on timeout).
set -u
G=${1:?usage: compile_remote.sh <group> <item> [file.lean]}; I=${2:?usage: compile_remote.sh <group> <item> [file.lean]}
case "$G" in *[!A-Za-z0-9_-]*) echo "group: letters, digits, - and _ only"; exit 2;; esac
case "$I" in *[!A-Za-z0-9_.-]*|.*|*..*|*.) echo "item: letters, digits, - and _ only, or a module name with dots"; exit 2;; esac
I=${I//./_}
ROOT=$(cd "$(dirname "$0")/.." && pwd); D="$ROOT/lean/.sandbox/$G"; mkdir -p "$D"; F="$D/$I.lean"
if [ -n "${3:-}" ]; then cp "$3" "$F"; else cat > "$F"; fi
[ -s "$F" ] || { echo "empty file"; exit 2; }
echo "== $F ($(wc -l < "$F") lines)"
SHEAF_GROUP="$G" SHEAF_FILE_TIMEOUT="${SHEAF_FILE_TIMEOUT:-60}" "$ROOT/tools/lean_file.sh" "$F"
