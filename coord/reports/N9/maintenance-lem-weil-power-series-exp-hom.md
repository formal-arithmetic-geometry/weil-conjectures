# N9 maintenance: lem-weil-power-series-exp-hom

2026-10-17, dispatcher key `lem-weil-power-series-exp-hom@new`, stage 2.

The first writer completed the statement and passed delivery preflight and
per-file compilation in dry run `6bd59f761b`. Its run directory ends in
`1792195180`. The independent reader (`1792196147`) then exited after Codex
exhausted HTTP 429 retries (request
`f20fb1df-a6ce-49d9-8f97-ba7aa206f0ac`). The following writer restarts failed
with the same provider status and different request ids. They did not report
a Lean, node or preflight error.

Two dispatcher faults amplified the provider interruption: missing `last.txt`
was reported as an empty `NOANSWER` instead of reading the terminal error in
`log.txt`, and an interrupted reader was rescheduled as a first writer.
A worker exit between reap and work could also be dropped before its result
was counted. No node, module or mathematical repair is justified by this
failure evidence.

Shared repair `6fb280508f56f3ab9401bdc8651a572b0e6bee43` was committed by the
concurrent Q53 maintenance while this investigation was in progress. It
retains provider diagnostics, retries transient transport failures within the
same role and budget, persists READY handoffs by stage and return revision,
and keeps ended workers until reap. N9 validated that committed version:
18 tests passed across `test_worker_transport.py`,
`test_dispatch_failure_classification.py`, and `test_stage2_handoff.py`.
Temporary fake CLI children were the only processes started by those tests;
no API requests or Lean/global builds were involved.

This maintenance adds
`tools/launcher/route-notes/lem-weil-power-series-exp-hom.md` and installs it at
the launcher's prescribed route-note path. It restores the independent second
reading for the already-running dispatcher, which retains old loaded code and
reads route notes on each new writer launch. New generic dispatcher code is
used at a normal service start; existing processes are preserved.

The next worker must read the complete stage-2 check brief, independently
review the existing statement, add its own second-reading report, and run the
usual per-file compile and delivery. The route note authorizes recreating
`.check` for this recovered reader role because the old dispatcher deletes it
on writer restarts. No second-reading approval is supplied by maintenance.
Failure counts remain informational and do not prevent further dispatch.
