# Verify the worktree is clean
if ! [ -z "$(git status --porcelain --ignore-submodules=all)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib WeilConjectures --git --check || exit 1

# Fetch build cache (not fatal: missing cache entries are compiled by the build below).
lake exe cache get || echo "warning: lake exe cache get failed; missing modules will be built locally"

# Verify everything builds. Lean sees all host cores, but agent pods have 4 CPUs and 16 GiB;
# one Lean process per core gets the container OOM-killed (exit 137). The heaviest single
# modules still take 6-8 GB of their own memory (e.g. ProEtale TensorSheaf, Kunneth StageConnecting,
# IntegersSheafHomologyTower), and Lake compiles up to LEAN_NUM_THREADS modules at once: with 3,
# three of them together exceed 16 GiB (several agent pods were OOM-killed this way on 2026-10-23).
# So cap the parallelism at 2 unless the environment sets it.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
lake build --wfail
