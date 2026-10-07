# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib WeilConjectures --git --check || exit 1

# Fetch build cache (not fatal: missing cache entries are compiled by the build below).
lake exe cache get || echo "warning: lake exe cache get failed; missing modules will be built locally"

# Verify everything builds.
lake build --wfail
