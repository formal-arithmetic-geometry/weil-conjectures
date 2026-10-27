# Q05 stale stage-1 claim repair — 2026-10-22

Item: `lem-weil-point-transformation-coefficient-descent`, dispatcher key `lem-weil-point-transformation-coefficient-descent@new`.

## Cause and evidence

Q107's accepted re-split landed at 2026-10-22 07:39:38 UTC in `9f173adbf6963e12b04c020d5e3386045990c054` (delivery `d01d79ab516`, reviewer `NT-cc-Q107-d01d79ab5`). It retained the parent statement and Lean record, supplied three statement-only obligations, shortened the assembly to 1452 characters, and resolved the stage-1 repair note. Stage 2 was already recorded by Q120 in `c36b1e27d43` on 2026-10-21. The parent's Lean proof remains unfinished; stage-1 completion does not claim Lean completion.

Q05 acquired a new claim at 2026-10-22 07:41:34 UTC (`t=1792654894.2587626`), after that landing. This claim was subsequently committed by build `1665f5677e1`. The first Q05 worker started at 07:42:32 UTC and correctly reported that the reviewed split was already complete. At maintenance start the dispatcher counted 54 failures and retained stage `1`.

The current `coord/queue.tsv` has no row for this node. The dispatcher nevertheless resumes each held, undelivered claim in `Group.work()`; `Group.server()` retains the saved stage when `claim.queue_stage()` returns no stage. The claim remained eligible through successive BLOCKED answers. Worker preflight correctly refuses an unchanged node, and the stage-1 live-wins rule correctly forbids re-splitting without a newly released repair order. The queue snapshot committed in `9f173adbf69` still contains this exact row (line 583): `lem-weil-point-transformation-coefficient-descent\t1\t5005\t\tnone\t`. This directly explains acquisition just after the landing. This is obsolete assignment data plus a missing dispatcher completion check, not a mathematical or Lean compilation failure.

## Repair

Under `SHEAF_LEAD=L-only flock coord/.merge.lock`, verified the passing Q107 review, resolved stage-1 repair note, stage-1 completion predicate, absent queue row, absent Q05 return and absent Q05 delivery branch. Then used the normal command:

`python3 tools/claim.py release Q05 lem-weil-point-transformation-coefficient-descent <maintenance reason>`

This removes only `coord/claims/lem-weil-point-transformation-coefficient-descent.lock` and appends the explanatory release to the running `coord/deliveries.log`. The log already had unrelated uncommitted journal entries; it remains managed by the normal bookkeeping/build process. The claim deletion and this audit report were committed in `878129a437480ad32f5253c4539dc135cb7e8300` under the merge lock, using Bin Wu's requested identity, without staging unrelated work. This follow-up records the exact stale queue evidence and the dispatcher method name; it changes only this report, backed up first with suffix `.maint-Q05-clarification-1792667953.bak`.

Before the release, byte-preserving backups were written next to both existing files with suffix `.maint-Q05-point-transformation-1792667953.bak`. This report is a new file with no previous version. Node and repair-note SHA-256 values were checked unchanged after the release. The completion and queue checks were repeated successfully.

No worker process was killed. No failure counter, queue priority, concurrency, admission setting or pause was changed. No Lean file changed, so no compiler or Lake command was needed.

## Next worker and protected follow-up

Stage 1 for this parent is complete. Do not submit an unchanged delivery, invent metadata changes to pass preflight, repeat the split, or reopen the resolved repair order. Further work belongs to the separately queued obligations or Lean stage; a new parent stage-1 repair requires an explicit released repair note.

The launcher owner should amend protected `dispatch_all.py` so a held stage-1 claim absent from the current queue is checked against the live stage-1 completion predicate and repair state before resumption. A completed claim with no released stage-1 repair, pending delivery or open return should be released as superseded. Revalidate the stage supplied by a held claim instead of retaining a stale stage when the item has left the queue. Preserve the human's instruction to dispatch every currently listed item, including legitimate released repairs. This is a completion check, not a failure-count cutoff, delay or concurrency limit. The launcher file was read only, as explicitly required.
