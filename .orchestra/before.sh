# Fetch latest build cache. Not fatal: Mathlib's cache server no longer has every blob of the
# pinned revision, and a failed `cache get` would otherwise abort the task before the agent
# starts. Modules whose cache is missing are compiled locally by the first `lake build`.
lake exe cache get || echo "warning: lake exe cache get failed; missing modules will be built locally"
