# Q117 i-topology maintenance

The repeated failures came from the Codex provider returning terminal HTTP 429 errors, compounded by a dispatcher handoff bug. The item's mathematical records were not the cause of the empty `NOANSWER` retries.

## Evidence

- Fourteen run directories were inspected. Eleven contain terminal `ERROR: exceeded retry limit, last status: 429 Too Many Requests`; several contain no worker command at all. Request IDs and log hashes are preserved in `attempt-evidence.json`.
- The configured provider is named `OpenAI`, but its configured endpoint is `https://the project server`. These logs establish rejection by the configured service; they do not expose whether the gateway limit is a token, request, concurrency, credit or upstream limit.
- Run `i-topology.1792193340` answered `READY i-topology: 1 new nodes, 0 Mathlib leaves`. The dispatcher started the independent reader `i-topology.1792194998`; that reader passed preflight but was then interrupted by a 429 without writing `last.txt`.
- The original dispatcher reads only `last.txt` for the final answer, discarding the terminal error in `log.txt`. It schedules a claimed, undelivered item as `new` after that reader exits. Thus an already prepared split repeatedly returns to authoring instead of completing independent review.
- `dry-run-retry.log` records a successful server preflight at temporary commit `7a37a04eff`; later workers printed the same success. The older `dry-run.log` stale-base/scope error was superseded by this retry. The current worker also passed two server `check_dag` checks. No `i-topology` entry was found in Q117 returns, deliveries or the inspected landing logs.

## Changes

- Installed `/home/ubuntu/weil-launcher-nt/route-notes/i-topology.md`, with backup `i-topology.md.maint-Q117-1792197036.bak`. The running dispatcher's existing launch method reads this file afresh for the next author attempt, so this correction works without restarting or killing its process. It directs that worker to validate the retained split and answer READY, restoring an independent second reader. It does not substitute maintenance for mathematical review.
- The same handoff is archived on the server at `tools/launcher/route-notes/i-topology.md`, with this diagnosis at `coord/reports/maintenance/Q117-i-topology.md` and evidence under `coord/reports/maintenance/Q117-i-topology-evidence/`.
- Concurrent maintenance sessions already own the shared dispatcher repair. Their server commits `6fb280508f` (Q53, transport retries and reader handoff) and `0abb765411` (NC, preserve interrupted reader reports in the same round) cover the general failure path. Their shared files were inspected, not overwritten by this maintenance. Further provider-capacity/session recovery work was in progress during this investigation.
- No node, Lean file, worker-authored report, dispatcher state, provider endpoint or global concurrency setting was changed by this maintenance. The active author worker was preserved. Every new maintenance artifact has a `.bak` snapshot; modified shared server documentation is backed up before editing.

Server commit for this maintenance: the commit introducing this report and `tools/launcher/route-notes/i-topology.md` (the final local REPORT.md records its exact hash).

## Validation

- Both deployed transport classifiers recover HTTP 429 from all eleven actual failed worker/checker logs.
- Eleven transport/classifier tests pass: bounded jittered retries, preserved reader prompt, no replay after a final answer, no retry of explicit quota/configuration failures, and correct separation from Lean compiler timeouts. These use temporary fake processes only.
- Replayed the original live dispatcher's `start()` method with a mocked process launch: it loads the installed Q117 route note, includes the READY recovery instruction, and retains the requirement for independent reading. No service restart is necessary for this route note.
- Current Python sources parse/compile. Fresh server preflight passed at temporary delivery commit `901f90a071`: `OK (not pushed) deliver/Q117/i-topology at 901f90a071: preflight passed`. The delivery tool also saved a durable stage-1 dry-run receipt for the second-reader handoff. Full output is in `maintenance-preflight.log`; this validation did not push a delivery branch.
- No Lean compilation was needed because this is a stage-1 transport/handoff repair; no Lake build was run. No other session's process was killed or signalled.

## Next worker

Keep `/home/ubuntu/weil-newtargets-sandbox/Q117/i-topology/` and its node, unit, citations and search records. Inspect concrete new failures, if any, and run `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q117 i-topology --no-push`. Once it passes, an author answers READY. The independent reader must check the sources/citations, write `## Second reading by Q117`, preflight and deliver using its own brief. A maintenance diagnosis or a mechanical preflight is not a completed second reading.

Failures remain counted and never disable this item. An API interruption should resume this work, not motivate a mathematical rewrite. Shared dispatcher code changes apply on its next normal service start; the installed item note is available to the already-running process on its next author launch.

Official OpenAI documentation was consulted for error semantics: https://developers.openai.com/api/docs/guides/error-codes and https://developers.openai.com/api/docs/guides/rate-limits. It supports distinguishing temporary throttling from quota/billing failures, but does not reveal this gateway account's actual limit.
