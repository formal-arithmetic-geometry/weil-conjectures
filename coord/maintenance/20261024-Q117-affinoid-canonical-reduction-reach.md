# Q117 canonical reduction: preserve the approved assignment's reach

The repeated failures are a queue reach mismatch. The item is unsplit,
unreviewed and incomplete under both stage1_completed(node) and
stage1_completed(queue_node(item)). Both DAG views resolve to the same live
repository's dag/nodes. There is no side completion to promote.

The item is reached at cut distance 41, through its sole direct citer
lem-trf-affinoid-canonical-reduction-finite-type, but queue_dist1 omits it after
withdrawn ancestors are excluded. The item itself is not withdrawn. The
maintenance evidence records the ancestors and exact queue simulation.

tools/nt_land_batch.py requires stage1() membership before applying a delivery.
When retirement correctly refuses this incomplete node, its notopen fallback
incorrectly calls the reach exclusion an unpromoted completion. The resulting
return asks for a worker rebase, although sandbox changes cannot alter that gate.

Retain this already assigned and independently approved item as an explicit root
in coord/preopen.txt, the existing mechanism for preserving allocated work.
The simulation and locked check must add exactly this item and remove none.
Withdrawn ancestors and the assumption/withdrawal records remain authoritative.

Replay the saved independent FIX at delivery
92316551c75fafea7ec1d9764540b4fd637b186e through unchanged tools/nt_land.py.
The saved review is local/verdicts/1/92316551c75fafea7ec1d9764540b4fd637b186e.json
and its adjacent review.md/fixes directory. It approves all eight steps and both
new statement-only nodes, with one citation correction: use the existing
lem-sfb-artin-tate-subalgebra-finite-type instead of the dropped per route node.
Preserve the saved fix exactly. Maintenance supplies no mathematical proof.

The normal landing tool rechecks current citations, review_split and DAG findings,
records the independent reviewer, closes the claim, removes the obsolete return
and delivery branch, and requests its usual queue refresh. Keep this preopen root
while the retained analytic assignment and its descendants are active.

Backups and receipts are outside the repository at
/home/ubuntu/weil-maint-bak/Q117-affinoid-canonical-reduction-1792853634/.
before.json records every original path, checksum and absent-file state; each
has a relative-path .bak. The approved review, reach simulation, commits, landing
output and post-landing verification are preserved there.

Protected-tool follow-up (report only): tools/nt_land_batch.py's land_chunk gate
and notopen fallback must distinguish an incomplete assignment excluded by active
reach from actual completion divergence. Report the reach cut and appropriate
coordination repair instead of instructing a worker to rebase. No landing tool,
review service, launcher-owned file, provider setting, failure count or concurrency
setting is changed by this repair. No Lean file changes or compilation are needed.

## Verified outcome

Reach repair committed as 12a9acaf5cc1259be3cba24ba1d7a32c61bffcc0.
The locked simulation added exactly this item (39 to 40), removing none.

The normal landing succeeded as 226e86e87dc3b25d3badde2ed076beed375a9c15.
The parent is split/reviewed PASS and complete in both DAG views; its proof
and dependencies match the saved independent FIX. Its stale return, claim and
delivery branch are absent. Both new statement-only children are open:
lem-trf-tate-spectral-generic-reduction-rank and
lem-trf-integral-generic-finite-algebra. All 18 initial backup checksums passed.

Next worker: do not re-split or re-push this completed parent for the historical
promotion error. Preserve the existing sfb Artin-Tate citation. Continue the two
new children only when assigned. The retained sandbox and original review-service
receipt remain historical evidence; the receipt still says returned and is
preserved unchanged. Use the reviewed live node and landing commit as current
completion evidence. No dispatcher counters or settings were changed.
