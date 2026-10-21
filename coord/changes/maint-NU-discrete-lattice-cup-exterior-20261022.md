# NU maintenance: completed stage-1 assignment

Item: `lem-sfb-discrete-lattice-cup-exterior` (stage 1).

Q08's delivery `79608c4068d` was independently reviewed by
`NT-cc-Q08-79608c406` and merged as `6fc80260023` at 2026-10-21
17:30:47 UTC+00 (commit display: 2026-10-22 01:30:47 +0800).
The delivery log records Q08 done at 17:30:46Z and ledger line 23191
records its accepted split. The live node is split and reviewed pass.

NU's claim was created at 17:30:53Z, seven seconds after the done log.
A queue row could still authorize a claim immediately after landing;
`claim.take` deliberately honors listed work (human instruction in commits
`19a02c3a093` and `13f40e5d647`). Subsequently the queue no longer listed
this node, but the held NU claim persisted. The dispatcher kept starting
stage-1 workers from that claim and its saved stage. Each retained the
accepted node and correctly failed the unchanged-node delivery check.
There is no NU delivery branch, open return, or repair note for this item.

Maintenance rechecked `claim.node_finished(item, "1") == True` and
`claim.queue_stage(item) is None`, then closed only the stale NU claim
with `tools/claim.py done` under `coord/.merge.lock`. The accepted DAG
node, proof, review, and Lean sources were preserved byte for byte.
Backups were made before touching the claim and delivery log:

- `coord/claims/lem-sfb-discrete-lattice-cup-exterior.lock.maint-NU-1792607519.bak`
- `coord/deliveries.log.maint-NU-1792607519.bak`

The launcher owner should reconcile held stage-1 claims against current
completion and repair records before relaunch, retiring completed work
once it is no longer queued. Respect explicit re-splits/released repairs
and stage-2 work. `dispatch_all.py` is protected from this maintenance
worker, so no dispatcher or admission code was edited. Failure counts
were retained; no retry restriction or concurrency limit was added.

Next worker: stage 1 is complete. Do not manufacture an item diff or split
it again. Any future stage-2 assignment must use the stage-2 brief and
normal prerequisite checks; this cleanup does not supply a Lean statement.
