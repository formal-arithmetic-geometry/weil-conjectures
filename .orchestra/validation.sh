# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib WeilConjectures --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds. Agent pods have a 4-CPU / 8 GiB limit but Lean sees all host cores;
# without a cap the full build runs one Lean process per core and the container is OOM-killed
# (exit 137), which kills the task. Cap the parallelism unless the environment already sets it.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
lake build --wfail
