# Q18 maintenance: etale sum right-adjoint coherence

The repeated stage-1 failures were stale assignments after completion. Q97's
reviewed re-split landed in b71b16a67a26748ef6af20f3fb2fb80537cfbb14 at
2026-10-22T11:51:44Z. The queue in that commit still listed the item for stage 1.
Q18 acquired the claim at 11:52:01Z. The queue later dropped the completed item,
but the dispatcher kept the held claim's cached stage 1 when queue_stage returned
None. Repeated dry runs correctly rejected the unchanged accepted item.

Maintenance verified the current item is split and reviewed, the repair note is
resolved, the live queue has no row, and Q18 has no delivery branch or open return.
Released the obsolete Q18 claim through tools/claim.py release under the merge
lock and recorded the reason in coord/deliveries.log. This is reconciliation of
completed work, with no new mathematical delivery or abandonment. The node,
repair note and Q18 return file were verified byte-identical across the change.

Backups of the deleted claim and pre-change deliveries log are retained at
/home/ubuntu/cc1/maintenance-Q18-1792699281/*.bak.

The launcher owner should reconcile held stage-1 claims against live completion
when a server queue lookup returns no stage, rather than retain the old stage
and start another worker. Confirm no released stage-1 repair and no outstanding
delivery or return before releasing; absence from the queue alone is insufficient.
Keep the human's listed-item dispatch rule and failure-count policy. No launcher
code was edited by this maintenance task.

There is no further stage-1 task on this item without an explicit new repair.
Retain Q97's accepted split and the Q84 Lean record. Let the live queue assign
remaining work on the four new prerequisite nodes; do not edit the parent merely
to satisfy the unchanged-item preflight gate.
