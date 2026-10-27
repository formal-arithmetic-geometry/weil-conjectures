# Maintenance: lem-route-sp-integral-twist-level-comparison

2026-10-26, group NB, dispatcher key
`lem-route-sp-integral-twist-level-comparison@new`.

The stage-1 split was delivered at `b80461a061a` and independently approved by
`NT-cc-NB-b80461a06`, then landed at `6066a6981e5312da742691bae48466c3976f417a`
on 2026-10-26 00:22:58 UTC (08:22:58 Asia/Shanghai). The approval is recorded in
`coord/ledger.md:16799`. The live node is `status: split` with a passing review;
there is no released repair note or pending delivery for this item.

The five subsequent failures were duplicate stage-1 assignments, not a defect in
the statement or proof plan. `tools/nt_land_batch.py:commit_one` closes the claim
and commits the split but never calls `queue_mark`/`md._qmark`. In contrast,
`tools/merge_delivery.py:cmd_merge` calls `_qmark("done", "1", [item])` immediately
after a successful merge. The batch path only requests an expensive background
queue refresh. Until that completes, the old stage-1 row remains claimable:
`tools/claim.py:take` deliberately honors a listed row even if the live node is
complete. NB reclaimed it at 00:23:20 UTC and then repeatedly retried the held
claim. Preflight correctly rejected an unchanged item. At maintenance inspection
the background refresh had removed the row, but the NB claim still existed and
there was no completion mark for the item in `coord/queue-states.tsv`.

Maintenance reconciles the existing successful landing through the existing
tools: `queue_mark.py done 1 <item>` and `claim.py done NB <item>`, after checking
the passing review, absence of a reopening, absence of an active delivery and
the stale claim's owner. The node, Lean source, sandbox, statement and proof
plan are unchanged. The original five failures are retained. Files affected by
the reconciliation have adjacent `.maint-NB-1792974737.bak` backups.

The durable code correction belongs in `tools/nt_land_batch.py:commit_one`:
after the split commit succeeds, while the merge lock is still held, publish
`md._qmark("done", "1", [item])`, matching the serial path. A failed commit must
not publish completion. Regression coverage should exercise both success and
failure, removal of stage-1 rows/tags, and an in-flight older queue write using
`queue_mark.done_since`. The user's maintenance instruction explicitly excludes
landing tools from edits, so this maintenance does not patch that file or the
review service. The operator must apply that correction in the owned tooling.

Validation: the live node's canonical `stage1_completed` and
`claim.node_finished(item, "1")` predicates are true. An isolated replay of the
existing queue-mark tool verifies removal of stale rows and tags, protection
against an older queue writer, and preservation of an unrelated row and a
separate stage-2 assignment. No Lean compilation is required for this record
repair. The existing `test_stage1_repair_queue.py` suite currently has four
failures (of six) before any edits; its synthetic graph is filtered by the live
progress-walk configuration. Those unrelated test fixtures were not modified.

The next worker should not split or resubmit this item at stage 1. Its accepted
split and original searches/citations are already preserved in the live DAG and
NB sandbox. `AlgebraicGeometry.ProEtale.spIntegralTwistLevel_comparison` still has
a `sorry`; this completion records the accepted stage-1 plan, not a proved Lean
theorem. Only an explicit released repair note can reopen the split.
