# Retired pruned stage-1 packet: lem-a1-principal-augmented-roos-descent

At 20261024T072906Z, maintenance verified that this unsplit node has no incoming
statement/proof dependency, is outside both target reach and cut reach, is absent
from stage 1 and coord/queue.tsv, and has no released repair note. It is not
mathematically completed. The parent lem-a1-roos-intrinsic-unit-comparison stopped
using it in the reviewed proof landing 3a3632211f1fc132c55065982b7205d9bf88b56d
(2026-10-22). The stale claim/return kept dispatching work after this pruning.

The approved delivery 5c0bfb68c22e9f01abeeeac8b6bb5810cedbb6ae is preserved at:
refs/superseded/Q07/lem-a1-principal-augmented-roos-descent/5c0bfb68c22e9f01abeeeac8b6bb5810cedbb6ae

Its reader verdict is PASS, retained in local/verdicts/1/5c0bfb68c22e9f01abeeeac8b6bb5810cedbb6ae.json.
The worker sandbox and exact approved node/report were also archived in the
launcher's maintenance directory
/home/ubuntu/weil-launcher-all/maint/Q07-lem-a1-principal-augmented-roos-descent-1792825749/evidence/.
The Q07 return below and the Q07 claim were backed up at /home/ubuntu/weil-maint-bak/20261024T072906Z-Q07-pruned-roos.
Only that return and claim are removed, and the exact delivery ref is archived.
The node, parent, other returns, failure counters and queue policy are unchanged.

The landing diagnostic was incorrect: tools/nt_land_batch.py tests membership
of Dag.stage1(), which also excludes unreachable nodes, then reports side-only
completion whenever queue_node exists and is incomplete. Both DAG paths actually
resolve to this repository. retire_stage1.retire_completed() correctly refuses
to call this unsplit node completed. Launcher-owned landing tools were not edited.
Their owner should distinguish pruned/unreachable from completed and archive
obsolete pruned packets rather than returning them for mathematical repair.

If a later reviewed split uses this lemma again, recover the archived payload,
rebase it, recheck cited statements, and deliver through the normal review path.
Do not add artificial reach or mark the node completed to bypass the landing gate.

Original stale return:

## lem-a1-principal-augmented-roos-descent (2026-10-24 04:57 UTC, branch head 5c0bfb68c22)

L: approved by the reader, but the landing refused it: NOT MERGED lem-a1-principal-augmented-roos-descent: lem-a1-principal-augmented-roos-descent: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
