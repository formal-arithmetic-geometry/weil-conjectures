# Restore the reviewed shared Néron lft-model definition

NM stage-2 repair `lem-sfb-finite-flat-neron-lft-descent@5aeaf671e` was retried
31 times because its return required Q92's reviewed `IsNeronLftModel`, but the
definition module and DAG node never reached the live branch. The Q92 delivery
is preserved at `refs/stale/deliver/Q92/lem-sfb-split-torus-extension-neron-lft`
with immutable head `c84990108f65c61c0fe6ec9c0b6a3b6958ae0c6b`.
Its independent review is PASS in
`local/stage2/reviews/cc__Q92__lem-sfb-split-torus-extension-neron-lft__c84990108f65/review.md`.

The server's stale-branch sweeper archives deliveries older than three hours
when the group no longer owns the item, without checking accepted reviews or
consumers waiting for their new definitions. The dispatcher log records Q92's
ownership loss at 14:57 +08; the worker nevertheless delivered at 15:17 +08.
The return required NM to wait for that definition, although it was never
published. Later Q98 and other deliveries independently supplied incompatible
interfaces for the same node; none was live when this recovery began.

Recover only the two shared-definition files unchanged from the reviewed
delivery. Do not replace the split-torus theorem or any existing mathematical
statement. The recovered definition was checked first in a private sandbox by
`SHEAF_GROUP=NM-maint-neron-1792849945 SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`;
exit 0, 8.4 seconds, no diagnostics. The recovered definition contains no sorry.

## Files and backups

- `lean/Sheaf/AlgebraicGeometry/NeronLftModel.lean`: absent before recovery = True; unchanged from `c84990108f65c61c0fe6ec9c0b6a3b6958ae0c6b`; SHA256 `4dadcf9cd116936b6fd43843595f8c28f1fc30ff4d4aa65199d90ec1b4832e53`. Backup: `lean/Sheaf/AlgebraicGeometry/NeronLftModel.lean.maint-NM-neron-1792849945.bak`.
- `dag/nodes/sec-six-functors-basics/def-sfb-neron-lft-model.json`: absent before recovery = True; unchanged from `c84990108f65c61c0fe6ec9c0b6a3b6958ae0c6b`; SHA256 `b275ad7b9058c03af6d7eb29fe9dc9a27dcc207b6022a5563bf7f50e49a84a85`. Backup: `dag/nodes/sec-six-functors-basics/def-sfb-neron-lft-model.json.maint-NM-neron-1792849945.bak`.

This note is new; its `.bak` preserves its initial text. Existing unrelated
working changes and dispatcher counters were not changed. No protected tool,
concurrency setting, admission policy or landing service was edited.

## Handoff

NM's retained repair already imports `Sheaf.AlgebraicGeometry.NeronLftModel`
and uses `IsNeronLftModel N' G_E' e'` / `IsNeronLftModel N H e`.
Keep its duplicate `GroupScheme/NeronLftModel` module and duplicate node copy
absent. Re-run its standard dry run and deliver through the normal worker path.
Other pending Néron deliveries must rebind to this canonical reviewed interface.

The protected stale-branch/review/landing owners should reconcile successful
reviews and published shared definitions before archiving a delivery that has
lost its original claim. Repair missing prerequisite publication, without any
retry cap, throttle, or pause. This is a tool follow-up, not a reason to stop
dispatching unfinished work.
