# Seed the project's build output from the latest published build of `slopmaster2`, if any
# (/tmp/weil-shared/build, refreshed by the maintainer after every merge). Lake only reuses
# artifacts whose inputs still match, so this is always safe and saves recompiling everything
# the task did not change.
if [ -d /tmp/weil-shared/build ]; then
  mkdir -p .lake/build && cp -a /tmp/weil-shared/build/. .lake/build/ 2>/dev/null \
    || echo "warning: could not seed .lake/build from /tmp/weil-shared/build"
fi
# Fetch latest build cache. Not fatal: Mathlib's cache server no longer has every blob of the
# pinned revision, and a failed `cache get` would otherwise abort the task before the agent
# starts. Modules whose cache is missing are compiled locally by the first `lake build`.
lake exe cache get || echo "warning: lake exe cache get failed; missing modules will be built locally"

# Cap Lean's parallelism for every command the agent runs. Agent pods have 4 CPUs and 16 GiB, but
# Lean sees all host cores, so a plain `lake build` starts one `lean` per core and the pod is
# OOM-killed. The agent's shell sources these files, so the cap applies unless a command sets its own.
for f in "$HOME/.bashrc" "$HOME/.profile"; do
  grep -qs 'LEAN_NUM_THREADS' "$f" || echo 'export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"' >> "$f"
done

# Run at most one Lean build at a time in the pod, with at most 3 Lean threads. A `lake` wrapper
# placed first on PATH takes /tmp/lake-serial.lock for every command that compiles or runs Lean
# (`lake build`, `lake env …`, `lake exe …`, `lake test`, `lake lint`) and caps LEAN_NUM_THREADS at 3.
# Agents and their sub-agents otherwise start several builds or `lake env lean` checks at once, and
# the pod is OOM-killed at its 16 GiB limit (often taking the agent itself with it). Commands that
# do not compile anything (`lake update`, `lake --version`, …) are not serialised. A `lake` started
# by another `lake` already holding the lock does not wait for it again. The lock file is separate
# from any lock the agent takes itself, so wrapping a build in `flock /tmp/lean-build.lock` as well
# cannot deadlock.
mkdir -p "$HOME/.local/lake-serial-bin"
cat > "$HOME/.local/lake-serial-bin/lake" <<'WRAPPER'
#!/bin/sh
# lake wrapper installed by .orchestra/before.sh: one Lean build at a time per pod, <= 3 threads.
self_dir=$(cd "$(dirname "$0")" && pwd)
real=$(PATH=$(printf '%s' "$PATH" | tr ':' '\n' | grep -vxF "$self_dir" | paste -sd: -) command -v lake) \
  || { echo "lake wrapper: no lake on PATH" >&2; exit 127; }
case "${LEAN_NUM_THREADS:-}" in ''|*[!0-9]*) LEAN_NUM_THREADS=3 ;; esac
[ "$LEAN_NUM_THREADS" -gt 3 ] && LEAN_NUM_THREADS=3
export LEAN_NUM_THREADS
case "${1:-}" in
  build|env|exe|test|lint)
    [ -n "${LAKE_SERIAL_LOCK_HELD:-}" ] && exec "$real" "$@"
    LAKE_SERIAL_LOCK_HELD=1; export LAKE_SERIAL_LOCK_HELD
    exec flock /tmp/lake-serial.lock "$real" "$@" ;;
esac
exec "$real" "$@"
WRAPPER
chmod +x "$HOME/.local/lake-serial-bin/lake"
for f in "$HOME/.bashrc" "$HOME/.profile"; do
  grep -qs 'lake-serial-bin' "$f" || echo 'export PATH="$HOME/.local/lake-serial-bin:$PATH"' >> "$f"
done
