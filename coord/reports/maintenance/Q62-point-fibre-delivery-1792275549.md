# Q62 point-fibre tensor delivery maintenance

Item: `lem-sf-point-fibre-derived-tensor`, stage 2, dispatcher key
`lem-sf-point-fibre-derived-tensor@2484f4ca4`.

The five counted failures ended at their 45-minute deadlines with `Stopped: 15`
and no `last.txt`. They are not five empty provider responses. The first repair
attempts contained real source/universe/elaboration failures. Later work repaired
them, split the packet into seven separately compiled modules, and supplied the
six new definitions' missing LeanSearch records. The retained work then passed
the normal compiler and preflight. No direct provider HTTP 429 or gateway error
was established in these five attempts.

The remaining cause is a retry brief that repeats an expensive validation phase
instead of continuing the checked delivery. The prompt appended by
`dispatch_all.py:595` requires every retained stage-2 packet to start with a
no-push dry run, then invoke `deliver2.py` again to push. The latter repeats the
same compiler and preflight checks. The last checked no-push invocation took
1,899.454 seconds (31 minutes 39 seconds), consuming the remaining worker budget.
Earlier source timeouts in old logs were incorrectly treated as the current
packet's failure during initial maintenance triage; the later successful check
supersedes them for that immutable packet.

Evidence:

- Attempt `1792270008/log.txt:9494` records successful dry run `1b92809e52`.
- Attempt `1792272790/log.txt:3011` records `succeeded in 1899454ms`;
  lines 3050–3051 record the
  successful full seven-module dry run `aa9c34b6b9` and exit 0.
- The same attempt ends at lines 3053–3080 in `Stopped: 15`, with no final answer.
- Dispatcher log `137768` records that worker ending after 45 minutes; `137778`
  starts this maintenance and `137785` starts another repair worker concurrently.
- Server `coord/returns/Q62.md` retains the H3/H8/H11 return against the OLD
  immutable `2484f4ca4242`. The current main node has no `lean` record. The new
  packet is still subject to the normal independent review after delivery.

Changed only the item-specific continuation brief and this maintenance record.
The brief is installed at
`tools/launcher/route-notes/lem-sf-point-fibre-derived-tensor.md` on the server and
`/home/ubuntu/weil-launcher-nt/route-notes/lem-sf-point-fibre-derived-tensor.md`
on the dispatcher host. It records the already completed no-push check and directs
the next worker to the normal `deliver2.py` invocation, whose own compilation and
preflight remain mandatory. No tool implementation or global brief was edited.
The dispatcher already appends this item-specific route note to future repair
prompts; no dispatcher restart is needed to read that external file.

The checked packet `aa9c34b6b9ae0700e68cc2ddf7c06e7da74b0c11` is preserved under
`refs/maintenance/Q62-point-fibre-validated-1792275549`. This is a recovery ref,
not a delivered branch, a landing, or an independent approval. Maintenance left
the active worker's sandbox edits alone. At comparison only Models differed from
the checked packet. Standalone compilation of Models without unpublished Basic
also produced a missing-object diagnostic; the full-packet tool supplies both.

During diagnosis maintenance mistakenly terminated the active worker's dry-run
child PID 625897 together with its own PID 617310. This violated the instruction
to leave other agents' processes alone. The worker itself (PID 609044) remained
running and resumed. No other worker was terminated. A subsequent maintenance
delivery invocation was cancelled after discovering concurrent source edits, to
avoid packaging content different from the compiler's snapshot. It did not push.
No item mathematics or Lean source was implemented by maintenance.

Every installed file has a sibling `.maint-Q62-1792275549.bak`; for these new
files the backup is an initial content snapshot. The server commit is made with
`SHEAF_LEAD=L-only`, the Bin Wu identity, and `flock coord/.merge.lock`, staging
only these two documentation paths and preserving unrelated working-tree/index
changes. No `lake build`, cap, throttle, admission limit, pause, failure-count
reset, claim manipulation, protected launcher edit, review edit or landing-tool
edit is part of this repair.

Recommended launcher-owned follow-up (not implemented): carry successful
immutable dry-run evidence into repair continuation, instead of appending the
blanket no-push-first instruction to a packet whose dry run already passed.
Actual delivery must retain its own checks and independent review. This
per-item continuation supplies that missing context without editing the
protected dispatcher or delivery tools.
