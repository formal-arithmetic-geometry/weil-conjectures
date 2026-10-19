# Q130: left proper derived cell colimits — provider failure recovery

Date: 2026-10-17. Item: lem-cbc-left-proper-derived-cell-colimits, stage 1,
dispatcher key lem-cbc-left-proper-derived-cell-colimits@new.

## Cause

The initial author attempt 1792193049 ran for 40 minutes and returned READY
after server preflight passed at delivery candidate 823c94cd6f. The dispatcher
launched the independent reader at 08:04:34 Asia/Shanghai. That reader, attempt
1792195474, ended at 08:10:53 with terminal HTTP 429 errors and no last.txt.
The dispatcher reduced the missing answer to NOANSWER and launched another
new author. Fourteen subsequent captured failures, through 1792196923,
ended with the same terminal provider diagnostic. Attempts that did run tools
also passed server preflight. There was no delivery branch or Q130 return for
this item when investigated, and no failed landing that could explain it.

The configured OpenAI provider routes through the project server. A read-only
web-tool request during maintenance itself returned gateway_concurrency_limit:
Concurrency limit exceeded for account, please retry later. This corroborates
a provider capacity incident. The launcher configured 700 worker slots and
30 per-request retries; immediate fresh worker restarts discarded session and
reader phase and contributed to congestion. No evidence required changing
the item's mathematical statement, proof, dependencies or Lean module.

## Repair

Concurrent maintenance installed the common fixes while this incident was
being investigated:

- a1a68055f2: tools/launcher/codex_retry.py, its tests and codex-retry.md;
  the active ~/.local/bin/codex entry point now routes dispatched workers
  through this supervisor. It retries temporary 429 failures with jitter,
  resumes the exact session, respects the original budget, and emits a
  useful BLOCKED diagnostic if recovery is exhausted. The original binary
  and entry-point backup are retained. This takes effect for new workers
  without killing or restarting the existing dispatcher.
- 6fb280508f: tools/launcher/dispatch_all.py preserves interrupted reader
  handoffs by delivery key. Dispatcher source edits take effect on its next
  normal start; the entry-point supervisor already covers new processes
  launched by the existing dispatcher.

This Q130 maintenance adds tools/launcher/route-notes/
lem-cbc-left-proper-derived-cell-colimits.md and this incident record.
The route note is also deployed at /home/ubuntu/weil-launcher-nt/route-notes/
lem-cbc-left-proper-derived-cell-colimits.md, which the current dispatcher reads
when launching an author retry. It directs that worker to validate retained
work and hand it to the required independent reader, without restarting the
whole split or manufacturing a review. Existing files are backed up before
replacement; new handoff files have .bak snapshots. No dispatcher state,
failure count, claim, delivery or mathematical record is rewritten here.

## Validation and next worker

The common recovery suite passed all 11 fake-CLI regressions during Q130
maintenance, including exact-session resume, startup failure, bounded
exhaustion, deadline, cancellation, provider concurrency diagnostics and
permanent-error handling. No model worker was started for these tests.
A retained copy and SHA256 manifest of the Q130 sandbox and an attempt-by-
attempt evidence table are in the maintenance working directory:
/home/ubuntu/weil-launcher-all/maint/
Q130-lem-cbc-left-proper-derived-cell-colimits-1792196672/.

Use the existing sandbox and follow the assigned brief. A successful dry run
is not an independent reading. The current author retry was already validating
the retained candidate when this note was written. Complete the normal
second-reader and server landing path; the maintenance task does not bypass it.
If the provider remains saturated, retain the supervisor's concrete diagnostic
and sandbox. Failure counts remain historical counts, never stop conditions.
No Lean files changed, no compiler or lake build ran, and no process was killed.
