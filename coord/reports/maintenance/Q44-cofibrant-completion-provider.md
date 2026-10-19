# Q44 cofibrant-completion maintenance incident

Item: lem-coef-cofibrant-completion-nerve-equivalence, stage 1, dispatcher key
lem-coef-cofibrant-completion-nerve-equivalence@new, 2026-10-17.

## Cause and evidence

The dispatcher counted ten empty NOANSWERs because raw Codex executions
exhausted provider HTTP 429 retries without writing last.txt. All ten failed
runs (1792195498, 1792195531, 1792196123, 1792196183, 1792196230,
1792196280, 1792196368, 1792196407, 1792196459, 1792196563) have a terminal
429 diagnostic in /home/ubuntu/weil-launcher-all/run/Q44/<item>.<run>/log.txt.
The first of those was a reader check after author run 1792192818 returned
READY. The old dispatcher then repeatedly started fresh authors instead of
preserving the interrupted reader handoff. The blank state note concealed the
provider cause. No item-specific return or landing failure explains this run
sequence. Maintenance made no mathematical changes; an independent reader
remains responsible for finding and repairing any content faults.

## Shared repair available and provider supervisor deployed

Server commits a1a68055f2 (provider retry/session supervisor), 6fb280508f
(transport diagnostics and durable reader handoffs), a5ae0952c3 (explicit
resume supervision), 0fa398c792 (missing saved-session recovery), and
86f2f12625 (prepared stage-1 packet recovery) address the shared launcher
failure. These were concurrent maintenance changes, not duplicate code
changes in the Q44 investigation.

Relevant canonical paths are tools/launcher/codex_retry.py,
tools/launcher/worker_transport.py and tools/launcher/dispatch_all.py.
The launcher host uses /home/ubuntu/.local/bin/codex ->
/home/ubuntu/weil-launcher-all/codex_retry.py. Its original executable link
was retained as /home/ubuntu/.local/bin/codex.maint-NK-1792196275.bak.
Existing maintenance .bak files beside the canonical sources preserve their
previous contents.

The running dispatcher PID 2532170 started at 04:28, before the recent
dispatcher source changes. Those in-process changes load on its next ordinary
supervisor restart. The executable retry wrapper already applies to newly
spawned children, including the current Q44 reader. No unrelated process was
stopped or restarted by this maintenance. The route note preserves this item
if that older dispatcher needs another author attempt.

The Q44 investigation adds only
 tools/launcher/route-notes/lem-coef-cofibrant-completion-nerve-equivalence.md
and this incident record, and deploys the route note to
/home/ubuntu/weil-launcher-nt/route-notes/ on the launcher host. Both server
documents are new files with .bak copies. No node, proof, dependency, Lean
file, dispatcher state or running process was changed by this investigation.

## Verification and next worker

The server launcher tests test_codex_retry.py, test_worker_transport.py and
test_dispatch_failure_classification.py passed: 28 tests. The launcher-host
supervisor suite passed 11 tests and both supervisor and dispatcher passed
Python syntax compilation. No Lean compilation or Lake build was needed.

Author run 1792196979 returned READY with zero new nodes and zero Mathlib
leaves after server preflight passed at ffc0da0f35. Its retained sandbox is
/home/ubuntu/weil-newtargets-sandbox/Q44/lem-coef-cofibrant-completion-nerve-equivalence.
Its report also records successful server check_dag and review_split checks.
These mechanical and author checks are not independent reader approval.

The dispatcher subsequently launched reader run 1792197977 through the
installed retry wrapper (codex-retry.json exists). That reader was still
running when this record was written. Let the ordinary dispatcher continue;
inspect that run and any delivery outcome before retrying. Keep the saved
packet and obey the assigned author/reader role. Do not reset the historical
failure counter or impose a retry cutoff. Future author/repair briefs load
the new route note automatically; independent reader briefs remain intact.

The local maintenance REPORT.md has the final commit identifier and the
absolute evidence paths.
