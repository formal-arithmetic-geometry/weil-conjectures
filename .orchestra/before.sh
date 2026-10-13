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
