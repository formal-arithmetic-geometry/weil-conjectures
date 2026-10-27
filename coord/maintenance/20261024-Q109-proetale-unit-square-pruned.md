# Q109: withdraw a pruned stage-1 unit-square assignment

Audited 2026-10-24T09:27:00Z under coord/.merge.lock. The item is unsplit and NOT completed.
The repository and queue read the same dag/nodes directory. There is no side
completion to promote. Its sole incoming statement/proof dependency is from
lem-sf-native-adic-pullback-frobenius-mates. That parent's accepted stage-2
record landed in f8a679b06ed3b0ecdd633c52070da177e8bad083 (2026-10-22), recording
the existing native declarations of WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate.
The parent's module is closed according to the live completion predicate.
The item is in unrestricted reach at distance 18, but absent from cut reach,
Dag.stage1(), coord/queue.tsv and the target list. No stage-1 repair is owed.
It is therefore work pruned below completed Lean, not a finished theorem.

tools/nt_land_batch.py puts every item absent from stage1() into notopen. If
retire_completed refuses an unfinished node, the fallback claims a side-only
completion merely because queue_node exists and is incomplete. This misleading
message became a headed return, which dispatch_all.py's returned-item loop
prioritizes without the off-queue checks used by its ordinary held-item loop.
Rebases and successful dry runs cannot repair live reach. The 37 failures at
dispatcher key lem-sf-proetale-direct-image-unit-square@267f0bc9d count this stale handoff, not mathematical faults.
The exact packet has an independent PASS in local/verdicts/1/267f0bc9d79a8444dd2b92326a47f1deee407aca.json; the verdict's own
inference about promotion was based on that misleading diagnostic.

Archived approved packet 267f0bc9d79a8444dd2b92326a47f1deee407aca at
refs/superseded/Q109/lem-sf-proetale-direct-image-unit-square/267f0bc9d79a8444dd2b92326a47f1deee407aca.
Removed only its headed Q109 return and stale Q109 claim, and recorded a release
without abandonment or completion. Other return sections are byte-identical.
The item node, parent node, Lean source, worker sandbox, citations and searches
are retained. Backups of every changed file and the original delivery ref are
at /home/ubuntu/weil-maint-bak/Q109-unit-square-20261024T092659Z/; the new note has a prior-absence .bak.
The isolated commit index preserves other agents' uncommitted delivery-log
appends. This repair changes records only, so no Lean compilation is needed.

Protected tools were not edited. Their owners should distinguish actual
completion, prune below completed nodes, lost reach, and a genuine side/live
disagreement; archive obsolete packets rather than returning them for a proof
repair. The dispatcher should revalidate returned stage-1 eligibility just as
it does ordinary held work, honoring released repairs and in-flight deliveries.
Failure counts must remain historical evidence, never a dispatch cutoff.
No concurrency, admission, throttle, pause or failure-limit change is needed.

Next worker: no stage-1 work is currently owed on this item. If a future route
or released repair makes it eligible, recover this approved packet, rebase it,
refresh cited statements and preflight through the normal delivery path. Do
not mark the unsplit node done or add a dependency merely to force eligibility.

Unchanged SHA-256 evidence:
- dag/nodes/sec-six-functors/lem-sf-proetale-direct-image-unit-square.json: dfcaa6bb3dec0976b2c25f7db674d1eb71b60e7a5725b6918735d4afb9e6a17c
- dag/nodes/sec-six-functors/lem-sf-native-adic-pullback-frobenius-mates.json: 8dcff2d52447dc9490dd8b7e10b1e399026f84e528dfe8c2969aa37337f45f47
- lean/WeilConjectures/SixFunctors/ProEtale/Adic/ExchangeMate.lean: b59bc94a247abe5dc718db8fd8bf4e0af980eb0ce61b5f186325775b7a3787d1

Original stale return:

## lem-sf-proetale-direct-image-unit-square (2026-10-24 04:32 UTC, branch head 267f0bc9d79)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sf-proetale-direct-image-unit-square: lem-sf-proetale-direct-image-unit-square: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
