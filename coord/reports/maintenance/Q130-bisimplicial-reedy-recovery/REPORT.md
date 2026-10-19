# Q130 maintenance report

Item: `lem-coef-bisimplicial-reedy-division-calculus`, stage 2, dispatcher key
`lem-coef-bisimplicial-reedy-division-calculus@new`.

## Cause

The repeated failures were provider transport failures. All 12 ended attempt
directories from `1792195122` through `1792196979` end with `429 Too Many
Requests`, and none contains a final `last.txt`. Seven failed before any tool
action. The first log explicitly records `gateway_queue_full`, with the
provider message “Too many pending requests, please retry later”. The earlier
maintenance attempt `1792196633` also ended on HTTP 429 without a report.
`EVIDENCE.json` records every failed attempt, session ID, terminal error,
request ID and log hash. The dispatcher counter was 10 when captured; it was
not reset or used to stop this item.

The pipeline turned an absent final-answer file into an empty `NOANSWER` and
started a fresh session, discarding the interrupted conversation. Increasing
the CLI's request/stream retry counts to 30 had not prevented these exits.
The brief, permissions, DAG binding and landing tools did not explain the
recorded terminal failures. The server has no Q130 return for this item;
the delivery-log entry from N9 is its earlier stage-1 split, not a rejected
Q130 stage-2 delivery. Its statement dependencies have Lean bindings or a
Mathlib match. The unfinished Lean draft initially had elaboration errors,
but these were ordinary work in progress interrupted by provider failures.

## Repair and paths

A concurrent pipeline maintenance session installed the common fix while
this investigation was running. I verified and reused that fix instead of
writing a competing supervisor:

- Server commit `a1a68055f2` (NK maintenance), in `/home/ubuntu/weil-newtargets`:
  `tools/launcher/codex_retry.py`, `tools/launcher/test_codex_retry.py`, and
  `tools/launcher/codex-retry.md`.
- Installed launcher code: `/home/ubuntu/weil-launcher-all/codex_retry.py`.
  `/home/ubuntu/.local/bin/codex` points to it. Its hash matches the server
  source: `7eac61c1e98687d96aa763175523822b1760eed81a910146074d222f128ea7e8`.
  The package-managed binary remains the pass-through target for other calls.
- The supervisor matches dispatcher worker invocations, retries temporary
  429s with increasing randomized delays, and resumes the recorded session.
  It stays within the worker's original budget. Exhaustion writes an explicit
  `BLOCKED` answer with the request ID and preserves the sandbox. It does not
  treat authentication or quota failures as temporary recovery cases.
- I installed the Q130-specific handoff at
  `/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-bisimplicial-reedy-division-calculus.md`.
  This is read by the dispatcher's normal item route-note mechanism on the
  next author attempt. The server source is
  `tools/launcher/route-notes/lem-coef-bisimplicial-reedy-division-calculus.md`.
- I archived this report, `EVIDENCE.json`, and `verify_recovery.py` in server
  `coord/reports/maintenance/Q130-bisimplicial-reedy-recovery/`.
  The replay script is run on the launcher, where the original prompts live.

The Q130 handoff/evidence commit is recorded in the local `COMMIT.txt` beside
this report. It is committed on the server under `coord/.merge.lock` with
`SHEAF_LEAD=L-only` and author/committer `Bin Wu <844524296@qq.com>`.
Only the explicit Q130 paths are committed. Every file written by this task
has a `.bak`; new-file backups are empty because no prior file existed.
The installed wrapper and symlink also have their own NK maintenance backups.

No DAG statement, dependency, Lean source, dispatcher state, global slot
configuration or mathematical content was changed by this task. No process
belonging to another session was stopped. No global build was run.

## Validation

- Server `python3 tools/launcher/test_codex_retry.py`: **11 tests pass**.
  The first suite invocation used a concurrently updated test file and had
  one cancellation-test failure; its isolated rerun passed, and the complete
  final suite then passed in 0.45 seconds. Local suite: 11 tests pass.
- `python3 verify_recovery.py` in this working directory: **PASS**. It uses
  real temporary fake-CLI children, the actual Q130 terminal errors and the
  original brief. It verifies resumption of session
  `01a14743-ae52-7243-bfd4-fbda65686387`, retention of CLI options and original
  brief, and a request-ID-bearing `BLOCKED` on exhaustion. No model API calls.
- The existing Q130 worker `1792197005` remained active. Its log records
  successful sandbox and library compilation of
  `Sheaf.AlgebraicTopology.BisimplicialReedyDivisionCalculus`, one file at a
  time through the prescribed compile wrapper with a 60-second per-file
  limit (3.2 and 3.4 seconds). It continued completing the node record/report.
  This observation is a checkpoint, not independent mathematical approval.

Official documentation confirms that request and stream retry settings are
separate ([Codex configuration reference](https://learn.chatgpt.com/docs/config-file/config-reference))
and recommends increasing delay with jitter after temporary rate limits
([OpenAI rate-limit guidance](https://developers.openai.com/api/docs/guides/rate-limits)).
The specific gateway diagnosis comes from the local logs, not those docs.

## Next worker

Continue the existing sandbox at
`/home/ubuntu/weil-newtargets-stage2-sandbox/Q130/lem-coef-bisimplicial-reedy-division-calculus`.
Preserve its Lean draft and search evidence; follow the stage-2 brief,
complete/check the Lean binding and report, run the delivery dry run, and
hand off to the independent second reader. Do not redo the item's mathematics
because of the empty `NOANSWER` history.

The active worker started before the supervisor was installed; an already
running process is not retroactively supervised. Do not launch an overlapping
author or overwrite that worker's files. Future dispatcher calls use the
installed supervisor automatically. Provider capacity remains external: a
long outage can still exhaust the bounded retries, which now report the
actual failure instead of silently losing the conversation. This maintenance
does not claim that the item's stage-2 delivery is complete.
