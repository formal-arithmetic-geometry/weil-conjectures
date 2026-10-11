#!/bin/bash
# Sourced by the other tools. Sets:
#   SHEAF_ROOT   the project directory (the one holding tools/)
#   SHEAF_LEAN   the Lake project (lean/, a directory or a link; SHEAF_TREE, set by build.py, selects the build copy)
#   SHEAF_LIB    the library's top-level source directories under lean/, space separated (from coord/sheaf.env)
#   SHEAF_BUILD  the shared build output, lean/.lake/build/lib/lean
SHEAF_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
SHEAF_LEAN=$(cd "${SHEAF_TREE:-$SHEAF_ROOT/lean}" 2>/dev/null && pwd -P) || { echo "sheaf: no Lean project in ${SHEAF_TREE:-$SHEAF_ROOT/lean}" >&2; exit 2; }
# Settings: coord/sheaf.env for the project, then coord/machines/<host name>.env for this machine.
for _f in "$SHEAF_ROOT/coord/sheaf.env" "$SHEAF_ROOT/coord/machines/$(hostname).env"; do
  [ -f "$_f" ] && { set -a; source "$_f"; set +a; }
done
: "${SHEAF_LIB:?set SHEAF_LIB in coord/sheaf.env}"
SHEAF_BUILD=$SHEAF_LEAN/.lake/build/lib/lean
# Non-interactive ssh has no lake/lean in PATH (launcher, 2026-10-11 05:30 UTC).
case ":$PATH:" in *":$HOME/.elan/bin:"*) ;; *) PATH="$HOME/.elan/bin:$PATH";; esac
# The package's [leanOptions] (lean/lakefile.toml) as -D flags, so that a single-file compile applies the same options
# as the global build (relaxedAutoImplicit/autoImplicit = false, warn.sorry = false, ...); launcher's finding 05:30 UTC.
SHEAF_LEAN_OPTS=()
if [ -f "$SHEAF_LEAN/lakefile.toml" ]; then
  while IFS= read -r _l; do SHEAF_LEAN_OPTS+=("-D$_l"); done < <(awk '
    /^\[leanOptions\]/ {on=1; next} /^\[/ {on=0} on && /^[A-Za-z][A-Za-z0-9_.]* *= */ {
      line=$0; sub(/#.*/, "", line); split(line, kv, "="); k=kv[1]; v=kv[2]; gsub(/[ \t]/, "", k); gsub(/^[ \t]+|[ \t]+$/, "", v);
      gsub(/"/, "", v); print k "=" v }' "$SHEAF_LEAN/lakefile.toml")
fi
export SHEAF_ROOT SHEAF_LEAN SHEAF_LIB SHEAF_BUILD PATH
