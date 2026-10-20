#!/bin/bash
# Compile one Lean file, with 2 threads and a time limit.
# Usage: SHEAF_GROUP=<group> tools/lean_file.sh <file.lean>
#
# - The time limit is SHEAF_FILE_TIMEOUT, default 60 s.
# - A library file compiled here writes its .olean into the group's private mirror local/build/<group>/ of the shared build,
#   so the group's later compiles can import a module it has just landed, before the next global build.
#   The shared build itself is only written when a green global build is published (build.py); a compile waits while
#   that is happening, and one that fails while it happened is run again once.
# - A file of Lean's module system is compiled into several files (.olean, .olean.server, .olean.private, .ir,
#   .ir.sig, next to the .olean). All of them are the group's own in the mirror: the links to the shared build are
#   removed before the compile, so that Lean never writes through a link into the shared build (stage 3).
# - The options of the project's own library (`leanOptions` of the lean_lib Sheaf in lean/lakefile.toml, i.e.
#   autoImplicit = false) are applied to every file except those of the adopted source library: a file under
#   lean/WeilConjectures/ or lean/Comparator/, and a sandbox copy of one (a path with /WeilConjectures/ or a file
#   name starting with WeilConjectures_, the name tools/compile_remote.sh and the merge give it).
# - Which compiled file the mirror keeps is decided by source content, not by mtime (2026-10-17). A compile here
#   records next to the .olean, in <module>.src, the git blob hash of the source it compiled. A refresh keeps the
#   group's own files of a module when that hash is the hash of the module's current source in lean/ and differs from
#   the module's source in the commit of the last published build (local/builds/published.json): the group has a
#   newer source of its own, and the shared copy, however recent, was built from another one. Otherwise the shared
#   copy replaces the group's when it is newer, as before. (A shared build of an older signature had replaced the
#   group's SmoothPurity/Defs and broke the next compile of Poincare with an unrelated kernel error.)
source "$(dirname "$0")/sheaf_env.sh"
F=${1:?usage: tools/lean_file.sh <file.lean>}; [ -f "$F" ] || { echo "no such file: $F"; exit 2; }
F=$(realpath "$F")
# 2026-10-20 (b69): coord/sheaf.env sets SHEAF_FILE_TIMEOUT=60 for every compile, which also cut the tools' own
# scratch walks (tools/sorry_route.py asked for 900 s; its walks timed out from 07:01 that day under load and the route
# went stale). The 60 s rule is for library files; a tool scratch file under lean/.sandbox/_sheaf/ may set
# SHEAF_TOOL_TIMEOUT instead.
case "$F" in "$SHEAF_LEAN"/.sandbox/_sheaf/*) [ -n "${SHEAF_TOOL_TIMEOUT:-}" ] && SHEAF_FILE_TIMEOUT=$SHEAF_TOOL_TIMEOUT;; esac
LP=$(cd "$SHEAF_LEAN" && lake env printenv LEAN_PATH) || { echo "lake env failed in $SHEAF_LEAN"; exit 2; }
OUT=(); PARTS=()
OPTS=("${SHEAF_LEAN_OPTS[@]}")
case "$F" in
  "$SHEAF_LEAN"/WeilConjectures/*|"$SHEAF_LEAN"/Comparator/*|"$SHEAF_LEAN"/.sandbox/*/WeilConjectures/*|"$SHEAF_LEAN"/.sandbox/*/WeilConjectures_*) ;;
  *) OPTS+=("${SHEAF_PROJECT_OPTS[@]}");;
esac
refresh_mirror() {
  # Link what the shared build has and the mirror lacks; where the shared build is newer than a file the group
  # compiled itself, the shared one is the verified one and replaces it; drop links to modules whose source is gone.
  # A dangling link whose module still has its source is kept: the shared build is being rebuilt in place (a base move
  # rebuilds lean/.lake/build with lake, outside build.py, and does not touch $SHEAF_BUILD), and deleting the link then
  # left the module missing from the mirror until the next publish (X-mir, 2026-10-11).
  [ ! -e "$M/.stamp" ] || [ "$SHEAF_BUILD" -nt "$M/.stamp" ] || return 0
  mkdir -p "$M"
  local -A keep=(); local pub="" pfx="" r h cur
  pub=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("commit") or "")' \
        "$SHEAF_ROOT/local/builds/published.json" 2>/dev/null)
  pfx=$(git -C "$SHEAF_LEAN" rev-parse --show-prefix 2>/dev/null)
  while IFS= read -r own; do
    s="$SHEAF_BUILD/${own#"$M"/}"
    [ -e "$s" ] && [ "$s" -nt "$own" ] || continue
    r=${own#"$M"/}; r=${r%%.*}
    if [ -z "${keep[$r]+x}" ]; then
      keep[$r]=0
      if [ -f "$M/$r.src" ] && [ -f "$SHEAF_LEAN/$r.lean" ]; then
        h=$(cat "$M/$r.src"); cur=$(git hash-object "$SHEAF_LEAN/$r.lean" 2>/dev/null)
        if [ -n "$h" ] && [ "$h" = "$cur" ] && { [ -z "$pub" ] || [ "$h" != "$(git -C "$SHEAF_LEAN" rev-parse -q --verify "$pub:$pfx$r.lean" 2>/dev/null)" ]; }; then
          keep[$r]=1
        fi
      fi
    fi
    [ "${keep[$r]}" = 1 ] || ln -sf "$s" "$own"
  done < <(find "$M" -type f \( -name '*.olean' -o -name '*.olean.*' -o -name '*.ilean' -o -name '*.ir' -o -name '*.ir.sig' \) 2>/dev/null)
  while IFS= read -r l; do r=${l#"$M"/}; [ -e "$SHEAF_LEAN/${r%%.*}.lean" ] || rm -f "$l"; done \
    < <(find "$M" -xtype l 2>/dev/null)
  for x in "$SHEAF_BUILD"/*; do [ -e "$x" ] && ionice -c3 cp -asn "$x" "$M/" 2>/dev/null; done
  touch "$M/.stamp"
}
if [ -n "${SHEAF_GROUP:-}" ]; then
  M="$SHEAF_ROOT/local/build/$SHEAF_GROUP"
  refresh_mirror
  LP=${LP//$SHEAF_BUILD/$M}
  case "$F" in
    "$SHEAF_LEAN"/.sandbox/*) ;;
    "$SHEAF_LEAN"/*) R=${F#"$SHEAF_LEAN"/}; R=${R%.lean}; mkdir -p "$M/$(dirname "$R")"
                     OUT=(-o "$M/$R.olean" -i "$M/$R.ilean"); PARTS=("$M/$R.olean" "$M/$R.ilean" "$M/$R.olean.server" "$M/$R.olean.private" "$M/$R.ir" "$M/$R.ir.sig" "$M/$R.src");;
  esac
fi
compile() {
  local n=0
  while [ -e "$SHEAF_ROOT/local/PUBLISHING" ] && [ $n -lt 60 ]; do sleep 2; n=$((n + 1)); done
  [ -n "${SHEAF_GROUP:-}" ] && refresh_mirror
  [ ${#OUT[@]} -gt 0 ] && { rm -f "${PARTS[@]}"; git hash-object "$F" > "$M/$R.src" 2>/dev/null || rm -f "$M/$R.src"; }
  ( cd "$SHEAF_LEAN" && LEAN_PATH="$LP" timeout "${SHEAF_FILE_TIMEOUT:-60}" env LEAN_NUM_THREADS=2 nice -n 19 \
      lean "${OPTS[@]}" -R "$SHEAF_LEAN" "${OUT[@]}" "$F" )
}
T0=$(date +%s.%N); START=$(mktemp); compile; rc=$?
if [ $rc -ne 0 ] && [ $rc -ne 124 ] && [ "$SHEAF_ROOT/local/builds/published" -nt "$START" ]; then
  echo "A global build was published during the compile; compiling again."; compile; rc=$?
fi
rm -f "$START"
DT=$(awk -v a="$(date +%s.%N)" -v b="$T0" 'BEGIN{printf "%.1f", a-b}')
if [ $rc -eq 124 ]; then
  echo "Timeout after ${SHEAF_FILE_TIMEOUT:-60} s: the cause is a definition the file uses; find it and change it."; exit 124
fi
echo "Compiled in ${DT} s"; exit $rc
