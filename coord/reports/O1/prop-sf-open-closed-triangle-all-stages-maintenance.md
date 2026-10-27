# O1 stale stage-1 claim correction, 2026-10-22

Item: prop-sf-open-closed-triangle-all-stages.

The five-node re-split at worker head e3ccd2b1f28 was independently approved
by NT-cc-O1-e3ccd2b1f and landed as c19760dd3cf27cb24a290bc8ce4d090bf89ac379
at 04:31:25 UTC. Its repair note is resolved; the live parent is split with
seven proof steps. The server completion predicates confirm completion for
stages 1 and 2. It has no queue row, delivery branch, or open O1 return.

A new O1 claim was created at 04:31:51 UTC, 26 seconds after the merge, then
tracked by build commit 2944e832e49. The dispatcher retained stage 1 when
the server queue no longer supplied a stage, and repeatedly resumed that
held claim. Preflight correctly rejected the unchanged parent and stale
statement-only child copies; four children now have later live splits.

Maintenance closed only this obsolete claim with tools/claim.py done,
recorded the completion, and preserved adjacent .maint-O1-1792645695.bak
backups of the removed claim, delivery log, and repair note. This report
also has a backup. No mathematical node, Lean source, sandbox, launcher,
review service, or landing tool was changed. No process was terminated.

Launcher-owner follow-up: dispatch_all.py must reconcile held and pending
stage-1 assignments with live completion before resuming them. A completed
item absent from the queue with no explicit return or released repair
obligation should have its obsolete claim closed. Preserve queue authority
and genuine repairs. Failure counts must never determine eligibility;
do not introduce any concurrency limit, throttle, backoff, or pause.
That protected launcher file was not edited.

Next worker: there is no remaining stage-1 task. Do not manufacture a diff
or overwrite later child proofs to pass unchanged-file preflight. Resume
only for a genuine new queue/return/repair obligation, using current live
records. The old O1 BLOCKED note describes this stale assignment.
