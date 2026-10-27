# Maintenance reconciliation: lem-route-bounded-constructible-derived-complete-integral-is-triangulated

The stage-1 split was already accepted and merged in `ac048c8c32d` (delivery `4f369760fd6`, reviewer `NT-cc-NA-4f369760f`). The live node remains `status: split` with reviewer `pass`, which is the completed stage-1 state; its later proof landing `7ab28363fe7` does not reopen stage 1. There is no repair note, open return, or delivery branch.

The repeated BLOCKED runs came from stale coordination data: claim `NA` was left on the item since `2026-10-25T20:25:35Z`, and a stale stage-1 row remained in `coord/queue.tsv` and both batch tag files. The dispatcher therefore relaunched a stage that `node_finished(..., 1)` already reports complete, and each worker correctly refused the dry run because the accepted split was identical to `origin/sheaf-dag`.

This maintenance repair released the obsolete `NA` claim and marked stage 1 `done` with `tools/queue_mark.py`, removing the item from the queue and batch tag files. The claim release and queue-state mark were performed while holding `coord/.merge.lock`; backups with suffix `.maint-NA-lem-route-bounded-20261026.bak` were made for every coordination file touched. No node, statement, proof, or Lean file was changed.

The launcher still needs a protected-code follow-up: reconcile a held stage-1/2 claim against authoritative `node_finished`, absence of an open return or released repair note, and a missing queue row before relaunching it. A stale queue row can be recreated by a queue writer race, so the durable queue-state mark must be consulted. The protected launcher files were not edited.
