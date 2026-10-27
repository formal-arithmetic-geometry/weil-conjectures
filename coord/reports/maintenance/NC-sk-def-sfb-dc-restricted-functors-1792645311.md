# NC stale stage-1 claim reconciliation

Item: `sk-def-sfb-dc-restricted-functors`. Maintenance run: `1792645311`. Reconciled at 2026-10-22T05:05:56Z.

NL's reviewed split was merged by L at `ddc37f917ce3cafc3a116e99f227a5904e5c0d02`
(2026-10-22 04:20:00 UTC; reviewer `NT-cc-NL-226937356`). The repair note is
resolved and the live node remains split with reviewer PASS. NC acquired a new
claim at 2026-10-22T04:20:11Z, ten seconds after that merge, while a stale queue
snapshot could still offer the completed stage-1 item. The dispatcher retained
this held claim after the live queue dropped the item and repeatedly started
stage-1 workers. Their refusal follows coord/brief-stage1.md's live-state rule.

Under coord/.merge.lock, maintenance verified stage1_completed=true,
claim.node_finished(item, "1")=true, queue_stage=null, no NC return for this item,
and no deliver/NC branch. It then used tools/claim.py release with the explicit
superseded-completion reason. This is bookkeeping for completed work, not an
abandonment, a failure-count gate, or a pause. The release is recorded in
coord/deliveries.log. The node, its accepted split, repair note, Lean records,
and NL's review remain intact.

Backups before mutation:
- `coord/claims/sk-def-sfb-dc-restricted-functors.lock.NC-maint-1792645311.bak`
- `coord/deliveries.log.NC-maint-1792645311.bak`

No Lean file changed; no compilation or library build was needed. The former
worker had already exited before the release. No process was killed.

Next worker: there is no remaining stage-1 task for this item. Use the live node
and resolved repair note; do not split it again or fabricate a new delivery.
Future proof work must be assigned from the current stage/module queue.

The launcher-owned dispatch_all.py was not edited. The local maintenance
REPORT.md documents the missing completed-held-assignment reconciliation for
the launcher owner. Failure counts must remain informational only.
