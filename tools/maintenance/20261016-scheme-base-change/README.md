# Launcher repair artifacts

These patches belong to the launcher, not to the Lean package.

- `dispatch_all.patch`: preserve existing repair sandboxes and pass the previous
  worker's note to repair retries. Apply from `weil-launcher-all` after checking
  the diff against the current source. It is already installed there.
- `stage3-worker.patch`: identify zero-hole repairs correctly in the worker brief.
  Apply from `weil-launcher` to `worker-brief3.md`. It is already installed there;
  `weil-launcher-all/briefs/batch1/stage3-worker.md` is a symlink to that file.
- `test_repair_pipeline.py`: source-only sandbox and delivery-gate regressions.
  On the launcher run `python3 -m unittest -v test_repair_pipeline.py` from the
  directory containing this file. `REPAIR_TEST_DISPATCHER` and
  `REPAIR_TEST_DELIVERY` can select other source copies. Tests use AST extraction
  and temporary files, never a live dispatcher, SSH, worker, claim or Lean compiler.

The source patch needs the dispatcher's next start to activate; no process was
stopped for this maintenance. The worker brief and item route note are read anew
from disk when dispatching. See `coord/maintenance/scheme-base-change-20261016.md`.
