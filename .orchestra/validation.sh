# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib WeilConjectures --git --check || exit 1

# Fetch build cache (not fatal: missing cache entries are compiled by the build below).
lake exe cache get || echo "warning: lake exe cache get failed; missing modules will be built locally"

# Verify everything builds. Lean sees all host cores, but agent pods have 4 CPUs and 16 GiB;
# one Lean process per core gets the container OOM-killed (exit 137). The heaviest single
# modules take 8-10 GB, so cap the parallelism at 3 unless the environment sets it.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
lake build --wfail
