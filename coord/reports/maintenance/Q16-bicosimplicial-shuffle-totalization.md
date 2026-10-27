# Q16 maintenance: completed bicosimplicial shuffle claim

Item: `lem-sfb-bicosimplicial-shuffle-totalization`, stage 1, dispatcher key `lem-sfb-bicosimplicial-shuffle-totalization@new`.
Recorded at 2026-10-22T19:55:49.419236+00:00.

## Cause

The obsolete Q16 claim, rather than unfinished mathematical work, caused the retry loop.
Q23's accepted repair landed at `fd0210e29a5e22b1688b651ce466baa7f6fcaf06`
on 2026-10-22 at 10:59:08 UTC (the delivery log records completion at
10:59:07 UTC). It resolves the human's re-split repair, introduces three
statement-only child tasks, and leaves the parent as a 2,213-character,
four-step assembly with a passing Q23 stage-1 review. The pre-existing
N7 stage-2 interface was accepted at `116bc58a686`.

Q16's claim was created at 10:59:27 UTC, 19 seconds after that landing.
The dispatcher started its first worker at 11:00:21 UTC. The stale queue
window allowed a new claim on completed stage-1 work: `tools/claim.py take`
intentionally skips its completion checks while the item is still listed
(human decision of 2026-10-22). This queue window is distinct from the
persistent stale-claim bug.

At maintenance, the item is absent from `coord/queue.tsv`,
`coord/queue-batches.tsv`, `coord/queue-batches-all.tsv`, and
`coord/repairs.txt`; `claim.queue_stage` returns None. Both
`claim.node_finished(item, "1")` and `claim.node_finished(item, "2")` are
true. The repair note is resolved. There is no Q16 delivery branch or
open return for this item. Its surviving claim had a 72-hour TTL.

`dispatch_all.py:server` retains its recorded stage 1 when `queue_stage`
returns None; the held-claim loop in `Group.work` launches such an item again.
It has completion cleanup for stage 3 but none for stages 1 and 2. Thus
an off-queue completed claim kept generating stage-1 assignments. The
workers correctly obeyed `coord/brief-stage1.md`'s live-wins rule, and the
unchanged-node preflight correctly rejected their unchanged copies.
The sandbox and logs show this blocker even in attempts with no provider
error. Some later attempts recovered historical HTTP 429s and still
returned the same blocker; no provider repair is involved here.

## Repair

Under `SHEAF_LEAD=L-only flock coord/.merge.lock`, used the existing
`python3 tools/claim.py release Q16 lem-sfb-bicosimplicial-shuffle-totalization ...`
interface to release only the obsolete claim. This removes
`coord/claims/lem-sfb-bicosimplicial-shuffle-totalization.lock` and appends the
reason to `coord/deliveries.log`. This report is the new maintenance record.
No abandonment, parking, failure-count skip, concurrency cap, throttle,
admission limit, or pause was introduced.

Backups kept on the server:

- `coord/claims/lem-sfb-bicosimplicial-shuffle-totalization.lock.maint-Q16-bicosimplicial-1792698747.bak`
- `coord/deliveries.log.maint-Q16-bicosimplicial-1792698747.bak`

The local maintenance directory also holds
`sandbox-before-release.tar.gz.bak`, preserving the whole worker sandbox
before normal dispatcher cleanup can retire an unclaimed sandbox.

## Verification and handoff

- The item is no longer in `claim.held_by("Q16")`; its claim file is absent.
- `tools/claim.py take-many --with-stage Q16 lem-sfb-bicosimplicial-shuffle-totalization 1`
  returns `NO`: already completed for stage 1, nothing to claim.
- The current queues still omit it and the repair note remains resolved.
- SHA-256 checks confirm that the parent node, repair note, and Lean module
  were unchanged by this repair. No Lean compile was needed or run.
- The dispatcher state and all worker search/citation history were left intact.

No further stage-1 worker should split or redeliver this parent unless a
new stage-1 repair is explicitly released. Continue the three child tasks
through normal queue assignments:
`lem-sfb-free-bisimplex-projective-resolutions`,
`lem-sfb-universal-shuffle-homotopy-inverse`, and
`lem-sfb-finite-representable-matrix-totalization`.
The parent's `exists_shuffle` theorem still has a proof obligation; an
accepted split or stage-2 interface does not mean its Lean proof is done.

## Launcher-owned follow-up

Do not edit the protected dispatcher here. Its owner should revalidate
held stage-1/2 claims before relaunching: when a successful current queue
read omits the item, confirm completion for the recorded stage, no
applicable released repair, and no pending delivery/return, then use the
claim-release interface for obsolete completed work. Keep listed items
and genuine open repairs dispatchable regardless of failure counts;
do not infer completion from a failed/empty queue read. This preventive
change belongs in `dispatch_all.py`, which this maintenance task is
explicitly forbidden to edit. The current item's records are repaired
without that code change.
