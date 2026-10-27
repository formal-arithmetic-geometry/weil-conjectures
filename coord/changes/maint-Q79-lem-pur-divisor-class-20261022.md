# Q79 maintenance: stale stage-1 divisor-class claim

Recorded 2026-10-22T08:50:18.826344+00:00.

The accepted stage-1 split landed as 4add3a9b164e5e94a95948009950362e58080a8d
(Q108 delivery a57767b07c3, independent reviewer NT-cc-Q108-a57767b07) at
2026-10-22T06:59:39Z. The live node is split, its review passed, and its stage-1
repair note is resolved. The current queue.tsv, queue-batches.tsv and
queue-batches-all.tsv do not list this item. There is no Q79 return or delivery
branch requiring repair.

A stale Q79 claim survived with this exact record:

```json
{
  "who": "Q79",
  "t": 1792652454.9986365,
  "since": "2026-10-22T07:00:54Z"
}
```

The claim was created at 07:00:54Z, 75 seconds after the landing. The dispatcher
reads held claims regardless of current queue membership. When queue_stage is
absent it retains Q79's cached stage 1, then starts every undelivered held item
again after each BLOCKED result. Workers correctly obeyed the standing brief's
live-wins rule. Failure counts are evidence of this record/dispatcher mismatch.

Released only this obsolete claim using tools/claim.py release Q79, preserving
its original record and the delivery log in sibling .maint-Q79-1792658558.bak files. The release
is logged in coord/deliveries.log. No node, proof, repair order, Lean file,
launcher code, process or dispatch limit was changed.

Validation under coord/.merge.lock: the claim is absent, held_by(Q79) excludes
the item, and claim.take(Q79, item, stage="1") refuses it as already completed
without creating a new claim. Other work and all future released repairs remain
eligible through the normal queue.

Launcher follow-up (protected dispatch_all.py; not edited here): reconcile held
stage-1 claims whose queue stage has disappeared before retrying them. If the
live stage-1 predicate says completed, no released stage-1 repair reopens it,
and no outstanding delivery/return needs repair, release the obsolete claim.
Refresh the stage when the authoritative queue supplies a later stage. This is
completion bookkeeping, independent of failure counts, and adds no throttle,
pause or admission restriction. Respect explicitly queued work and released
repairs.

The next stage-1 worker should not duplicate Q108 or reopen the resolved repair.
There is currently no stage-1 assignment to perform. Future work follows a new
released repair note or the authoritative queue's stage and brief. Helpers
extracted by Q108 remain separate nodes with their own work records.
