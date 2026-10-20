# E8 quarantined retirement delivery regression (2026-10-20)

Item: `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions`, group E8,
stage 3, dispatcher key ending `@new`.

## Cause and deployed fix

The sync moved the duplicate from `lean/Sheaf/AlgebraicGeometry/` to
`quarantine/Sheaf/AlgebraicGeometry/`, retaining its `coord/rework.tsv` row. The
item also has a human-authorized retirement row in `coord/retire-items.tsv`.
The worker correctly retained a packet with one consumer import replacement,
the DAG attachment moved to the upstream twin, and the old original path in
`deleted.txt`. The old launcher rejected that required path before compilation
because it checked only the live `lean/` source. Repeated attempts did not
represent repeated mathematical failures.

While this maintenance investigation was running, a concurrent owner installed
the fix in `/home/ubuntu/weil-launcher/deliver3.py` at approximately 13:24 UTC.
This maintenance session did not overwrite that change. The deployed code now
accepts the corresponding quarantine source and creates missing parent
directories before writing the existing empty withdrawal module. It leaves the
quarantined original for the normal green-build reconciliation. `deliver3.patch`
records the exact deployed change; `deliver3.py.bak` is the pre-fix source and
`deliver3.py` is the tested deployed snapshot.

Deployed SHA-256:
`0f6471032f0406d2e60769fbfe70d5211498d8697a70b2e9b948a73a96d469a2`.

## Validation

- `python3 test_quarantined_retirement.py`: seven tests pass. The tests execute
  the actual manifest parser extracted from the deployed snapshot. They cover
  live and quarantined withdrawals, preservation of quarantine, missing source,
  simultaneous sandbox restoration, prohibited paths, and empty manifests.
- The deployed parser accepts the actual retained E8 `deleted.txt`.
- The retained consumer differs from its quarantined original by precisely the
  import replacement to the upstream twin. It compiled with
  `SHEAF_GROUP=ME8RETIRE SHEAF_FILE_TIMEOUT=60 bash tools/lean_file.sh ...` in
  3.8 seconds with no diagnostics.
- Its separate axiom probe also ran through `tools/lean_file.sh`, in 4.3 seconds:
  `SHEAF-PROBED 1`, no `SHEAF-AXIOM`. The only warning belongs to the appended
  tool probe's long line, outside the delivered source.
- The unchanged server preflight accepts an isolated packet at detached commit
  `78956e727a48228d0afc547e1f99d7e78fa80640` (base `3e284edd72`):
  `preflight OK (stage 3)`, review class CODEX. It recognizes the withdrawal as
  the item and the consumer as a restored module. This preflight used
  `SHEAF_COMPILE_ROOT=/nonexistent` for static checks; the consumer compilation
  and axiom probe above were performed separately with the required wrapper.

The detached validation commit was created on the server with author Bin Wu,
email 844524296@qq.com and `SHEAF_LEAD=L-only`, while holding the project's
`coord/.merge.lock`. It is retained only in
`/home/ubuntu/weil-maint-E8-retire-1792502308/preflight-worktree`; it was not
submitted as a worker delivery or merged into `sheaf-dag`.

## Next worker

Continue the retained retirement packet. Keep the obsolete original path in
`deleted.txt`; do not restore the duplicate beside it or edit the quarantine.
The delivery tool creates its normal empty withdrawal module. Keep the restored
consumer and twin DAG attachment. Refresh the sandbox report's historical
tool-failure paragraph after a current successful dry run, then use the normal
delivery route. Leave unrelated cluster repairs to their own workers.

The earlier dispatcher brief includes both REWORK and RETIRE instructions. The
explicit retirement instruction governs this duplicate; no mathematical proof
repair of the old duplicate is needed. A launcher-owner cleanup could avoid
printing both mutually exclusive instructions, but it is not needed for this
packet to pass. `dispatch_all.py` and all other protected launcher, review and
landing tools were not edited. No dispatch limits or pauses were added. The
worker sandbox, project Lean sources, DAG, quarantine, claims and rework records
were not changed by this maintenance session.
