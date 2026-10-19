# Q115 thm-trf-dualizing-complex-composition maintenance

The retry loop was caused by terminal provider HTTP 429 failures and lost
second-reader state. The item's mathematics was not the cause of the empty
NOANSWER notes. A new author run has now passed server preflight at
`58cc6c26d6` and returned READY. The dispatcher has started an independent
second reader, run `1792198499`, with `kind: check`; its review remains pending.

## Cause and evidence

The original author run `1792190649` passed preflight at `4c56fef94d` and
answered READY. The dispatcher started the second reader `1792192197`, which
was still waiting for validation capacity when its 46-minute run ended without
an answer. The dispatcher then started a **new author**, rather than resuming
the reader. Twelve subsequent historical logs end in terminal HTTP 429, several
before any worker command. The dispatcher read only absent last.txt files and
recorded empty `NOANSWER: ` notes. Its work() path could also drop an ended run
between reap and scheduling, so failure counts are not an exact run inventory.
`attempt-evidence.json` preserves paths, hashes, request IDs, outcomes and the
observed state. Its snapshot has 15 runs: two READY answers, twelve terminal
429 failures, and the interrupted original reader.

The configured service is named OpenAI but uses the Frenzy APIs gateway. The
logs do not identify its actual token/request/concurrency/quota limit. Starting
fresh sessions immediately repeated reading work under the same service
failure. No return, delivery or landing entry for this item was found in the
server's Q115 return file, deliveries.log or inspected cc1 landing logs.

An initial investigation mistook old NameError tracebacks in dispatch_all.out
for this run's cause. Those tracebacks predate the current dispatcher; its
source already has the quoted clone_prefix key. This maintenance did not
claim or install a fix for that historical error.

## Changes

- Installed the item-specific recovery note at
  `/home/ubuntu/weil-launcher-nt/route-notes/thm-trf-dualizing-complex-composition.md`.
  The already-running dispatcher reads route notes at the next author launch.
  It tells that worker to retain and validate the packet, answer READY and
  restore independent reading. It also resolves the contradictory retry
  sentence saying to deliver, and records the short-quotation and guessed-node-
  path diagnostics encountered by earlier workers. No mathematical route was
  written or changed by maintenance.
- The same note and evidence are archived in the server project under
  `tools/launcher/route-notes/thm-trf-dualizing-complex-composition.md` and
  `coord/reports/maintenance/Q115-dualizing-composition/`.
- Found a server `tools/launcher/codex_retry.py` regression accepting
  `exec resume --last ... UUID -`. Concurrent maintenance corrected the guard
  in `8846ae9192` and `7aa72985b8` before this session's installation. Verified
  the corrected server suite passes all 14 tests. The deployed local wrapper
  also excludes `--last`; this session preserved both versions.
- Copied the already-committed `worker_transport.py` from server commit
  `6fb280508f` into `/home/ubuntu/weil-launcher-all/worker_transport.py` when the
  local file was missing. Concurrent maintenance integrated the dispatcher
  source; this maintenance did not overwrite those source changes. A source
  backup was made at `dispatch_all.py.bak-Q115-1792197004`, but no edit to that
  file was made by this session.

Shared repairs installed by related maintenance are `a1a68055f2` (the CLI
recovery supervisor, now used by ~/.local/bin/codex), `6fb280508f` (transport
and handoff recovery), `0abb765411` (retain an interrupted reader's report),
and later capacity, session and durable stage-1 receipt changes. They are
attributed to their existing commits; this report does not claim their code
as Q115 work. The entry-point supervisor applies to new workers without
restarting the old dispatcher. In-memory dispatcher source changes apply on
its next ordinary start.

All changed existing files have adjacent `.bak` copies; new installed paths
have an empty `.bak` marker recording their previous absence. The server
installation and exact-file commit run with `SHEAF_LEAD=L-only`, exclusive
`coord/.merge.lock`, and Bin Wu <844524296@qq.com>. The final local report
records the exact Q115 server commit below.

## Validation and current state

- All twelve historical terminal failures are recognized by the deployed
  transport classifier. Twenty local transport, reader-resume and diagnostic
  regressions pass, including large failure counts remaining eligible.
- Replayed the original dispatcher launch method with a fake process and
  temporary sandbox: the Q115 note loads without a service restart, and the
  author READY/independent-reader requirements remain present.
- The server supervisor suite initially failed its `--last` exclusion case.
  All 14 tests now pass after the concurrent guard corrections; the suite
  is also rerun under the merge lock during installation.
- The real worker `1792197038` repaired the current quotation diagnostics,
  passed server preflight at `58cc6c26d6`, saved a durable stage-1 receipt and
  answered `READY ...: 0 new nodes, 0 Mathlib leaves`. This maintenance read
  its logs; it did not claim to author or independently review that split.
- The latest state snapshot shows independent reader `1792198499` running
  with `kind: check` and the original `@new` key. The failure count remains
  12 and `gaveup` is empty. No completed delivery is asserted.
- No Lean source changed or compiled, no Lake build ran, no dispatcher state
  or failure count was reset, and no process was killed or signalled.

## Next worker

Keep `/home/ubuntu/weil-newtargets-sandbox/Q115/thm-trf-dualizing-complex-composition`.
Read its current report and dry-run-final.log. Its eight citation excerpts
passed the server's minimum-length and verbatim checks. Earlier seven-citation
reports and failed dry runs are historical. Refresh quotations if shared
definitions change while validation queues; use node IDs to find files instead
of guessing their chapter.

An author retry must validate the saved packet and answer READY. The second
reader checks the current split against the sources, appends the required
`## Second reading by Q115`, preflights and delivers. Never infer completed
review from NOANSWER, a dry-run receipt or this maintenance report. Stage 1
uses DAG/split checks, without Lean or Lake. Failure counts keep accumulating
and never disable dispatch.

The [official OpenAI rate-limit guidance](https://developers.openai.com/api/docs/guides/rate-limits)
supports retrying temporary throttling with bounded exponential backoff and
jitter. The [error-code guidance](https://developers.openai.com/api/docs/guides/error-codes)
distinguishes rate limits from quota/billing errors. These sources cannot
determine this gateway account's actual capacity.
