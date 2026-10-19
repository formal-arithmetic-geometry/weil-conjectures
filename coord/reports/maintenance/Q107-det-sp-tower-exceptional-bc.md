# det-sp-tower-exceptional-bc: maintenance report

The cause is provider HTTP 429 exhaustion followed by immediate fresh-session
dispatch and loss of the terminal diagnostic. It is an infrastructure failure,
not evidence that the item's mathematics is wrong. All eleven completed runs
from `1792194680` through `1792196713` ended with the fatal Codex diagnostic
`ERROR: exceeded retry limit, last status: 429 Too Many Requests`; none wrote
`last.txt`. The dispatcher read only that absent file and stored `NOANSWER: `.
Its state reported 10 tries, so that counter is not a complete historical run
inventory. `attempt-evidence.json` records the individual paths and request IDs.

The launcher was configured for up to 700 workers and could create additional
maintenance sessions. Immediate replacements amplified the congestion and
repeated the session's reading work. The logs establish terminal provider
failures; they do not establish the provider account's exact capacity. The 429
after a logged `srvcheck.py` invocation was emitted by Codex, not by srvcheck.
No return, delivery or landing entry for this item was found on the server.

## Fix and deployment

Related maintenance sessions landed shared recovery fixes while this diagnosis
was in progress. I verified the installed fix rather than installing another
retry layer or overwriting their dispatcher changes:

- `a1a68055f2b73fe62674754cb95071667bd798ac` in
  `/home/ubuntu/weil-newtargets`: `tools/launcher/codex_retry.py`,
  `test_codex_retry.py`, and `codex-retry.md`. The deployed supervisor is
  `/home/ubuntu/weil-launcher-all/codex_retry.py`; the existing
  `/home/ubuntu/.local/bin/codex` symlink now points to it. It retries temporary
  provider errors with bounded exponential jitter, resumes the same session
  when known, keeps the original model and sandbox, and writes an explicit
  BLOCKED diagnostic on exhaustion. Authentication and quota failures are not
  retried. Its original entry point backup is
  `/home/ubuntu/.local/bin/codex.maint-NK-1792196275.bak`.
- `6fb280508f56f3ab9401bdc8651a572b0e6bee43` preserves reader handoffs and
  transport diagnostics in the server's dispatcher source. It was committed
  by the related Q53 maintenance session. Source changes require the next
  normal dispatcher start; the installed entry-point supervisor already
  applies to new workers launched by the current dispatcher.
- This maintenance adds the item-specific handoff at
  `tools/launcher/route-notes/det-sp-tower-exceptional-bc.md`, installed at
  `/home/ubuntu/weil-launcher-nt/route-notes/det-sp-tower-exceptional-bc.md`,
  and archives this diagnosis at
  `coord/reports/maintenance/Q107-det-sp-tower-exceptional-bc.md`. The commit
  receipt is recorded in `server-maintenance-commit.txt` beside this report.

The handoff is read by the existing dispatcher when it next starts a first
worker on this item. Existing files are backed up with an adjacent
`.maint-Q107-1792197036.bak` before replacement. The server installation runs
under `SHEAF_LEAD=L-only flock coord/.merge.lock`; the commit uses Bin Wu
`<844524296@qq.com>` and contains only these item-specific documentation paths.
Failure counts, claim eligibility and the mathematical sandbox were preserved.
No processes were killed and no Lean compiler or Lake build was run.

A standalone diagnostic prototype passed eight tests in this working
directory, but is deliberately retained only under `prototype/` and is not
deployed: the shared fixes already cover that behavior. It is not part of the
server commit.

## Validation

- All eleven historical terminal errors were recognized from the actual logs.
- The deployed recovery supervisor's 11 fake-CLI regressions passed locally
  and on the server, including session resume, startup retry, bounded
  exhaustion, deadlines, cancellation, permanent-error exclusions and real
  answer precedence.
- The server's eight transport/handoff regressions also passed.
- The exact Q107 command shape is covered by the installed supervisor, and
  the entry-point symlink resolves to it. `codex --version` still returns
  `codex-cli 0.162.1`. `deployed-recovery.json` records the checked script hash.

These checks establish deployment and recovery behavior; they do not promise
provider availability or certify the unfinished mathematical split. The
[official OpenAI rate-limit guidance](https://developers.openai.com/api/docs/guides/rate-limits)
supports bounded backoff with jitter and distinguishing temporary rate limits
from quota/billing errors. The visible CLI error does not provide a
Retry-After value.

## Next worker

Resume `/home/ubuntu/weil-newtargets-sandbox/Q107/det-sp-tower-exceptional-bc`.
The early attempt left a seven-step split, citations and search evidence; an
active worker was revising these during maintenance, so inspect their current
contents rather than assuming a fixed snapshot. Maintenance did not perform
the mathematics or mark this item delivered.

At inspection, the current worker was the pre-installation run `1792197037`,
PID `2585661`. It was left running. If it exits without an answer, the next
ordinary dispatch uses the installed supervisor; there is no need to restart
the dispatcher or delete its sandbox. Revalidate the current split against
the source and cited statements, complete the required report, run the server
checks and delivery dry run, and follow the first-worker/second-reader brief.
`NOANSWER: ` never constitutes a rejected proof or an accepted check. Look at
`codex-retry.json` in future runs for provider recovery information.
