# Q93 maintenance: lem-trf-weil-shriek-operator-fibres

2026-10-17, stage 1, dispatcher key
`lem-trf-weil-shriek-operator-fibres@new`.

## Cause and evidence

The ten counted failures were a pipeline incident. The available 13 worker-run
directories include eleven runs ending with provider `429 Too Many Requests`,
an initial 45-minute timeout, and the active recovery run `1792197037`.
For example, run `1792195418` passed server preflight at `5bb4a282ca` before
losing its final answer to HTTP 429 (request
`762004f9-8ba5-43a4-92d6-58b16ad5ccb4`). Several subsequent runs failed before
their first tool call. Run `1792196772` also contains a passed dry run before
its terminal 429 (`e5cc5252-a626-4346-91ed-ead131e803e9`).

The old dispatcher treated absent `last.txt` as blank `NOANSWER: `, retained
neither provider diagnosis nor the completed first-reader handoff, and started
fresh sessions. This amplified provider congestion: the launcher's configured
pool was 700 and a diagnostic snapshot found about 501 timeout workers with
their model children. Failure counts were not a reason to stop this item.

A separate reproducible tool race affected the active run. At approximately
08:40 +08, preflight rejected a stale base and changes to another group's
`def-trf-kernel-pushforward-maps` node/report. Neither unrelated file existed
in this sandbox. Shared worktrees share origin refs; concurrent fetches moved
the reference used for comparison after the delivery checkout. The repaired
tools pin the checkout commit through bundling and server preflight. The same
worker reran delivery without removing any sandbox file and passed at
`8b14a6161d`, saving `.stage1-ready.json` at 08:46:42 +08. Its earlier diagnostic
`check_dag` also passed. Initial worktree-capacity waits and normal upstream
citation drift contributed delay; neither explains the terminal 429s.

No server return, delivery or landing for this item was found during this
investigation. This is not a Lean compiler or item-module failure.

## Repairs and Q93 changes

Concurrent maintenance installed shared repairs while this incident was being
investigated. I verified and reused them instead of overwriting active work:

- `a1a68055f2`: `tools/launcher/codex_retry.py` and tests; bounded backoff and
  recovery after provider 429s. Runtime entry point `~/.local/bin/codex` points
  to `/home/ubuntu/weil-launcher-all/codex_retry.py`.
- `a5ae0952c3` and `0fa398c792`: supervise explicit resumes and recover from an
  unavailable saved session while preserving the original role and sandbox.
- `783eefd226`: `tools/launcher/deliver.py`, `srvpreflight.py`, `srvcheck.py`
  and regressions; immutable preflight baseline and correct metadata overlay.
  Runtime copies are in `weil-launcher-nt/deliver.py` and
  `weil-launcher-all/{srvpreflight,srvcheck}.py`.
- `f2419b5883`: `tools/launcher/stage1_handoff.py`, tests and dispatcher
  integration; a successful dry run records the exact sandbox fingerprints
  and can recover READY after final-answer loss. A receipt never approves a
  push or replaces an independent second reading.

The deployed wrapper also uses a FIFO provider-admission gate, currently 64
children with a one-second start interval and a 60-second 429 cooldown. This
works for new supervised children without restarting the old dispatcher and
counts legacy children while they drain. Other maintenance owns these shared
admission changes. This Q93 repair did not change global concurrency.

Q93-specific changes in the commit containing this report:

- `tools/launcher/route-notes/lem-trf-weil-shriek-operator-fibres.md`, deployed
  to `/home/ubuntu/weil-launcher-nt/route-notes/` for future worker briefs.
- This report and adjacent `.evidence.json`, preserving request IDs, run paths,
  state snapshot, successful dry runs, receipt and deployed tool hashes.
- Started a local, owned recovery helper using the tested
  `stage1_handoff.py Q93 lem-trf-weil-shriek-operator-fibres --watch-seconds 1800`.
  The dispatcher PID 2532170 predates the source repairs and does not reload
  its imported code. The helper bridges that run: it writes a recovered READY
  only after worker exit, with an exact current receipt, no existing answer,
  and an unchanged current state entry. It does not rewrite dispatcher state
  or signal any worker. Its PID/log are in the maintenance working directory.

Every installed Q93 file has an adjacent `.maint-Q93-1792197035.bak` snapshot;
local investigation artifacts have `.bak` siblings. No mathematical node,
Lean file, sandbox input, failure counter, claim or dispatch eligibility was
changed. No foreign process was stopped. No Lean compile or Lake build was
needed or run.

## Verification and next worker

On the server, all 32 tests passed using:

```
cd /home/ubuntu/weil-newtargets/tools/launcher
python3 -m unittest test_preflight_base test_codex_retry test_codex_retry_resume test_codex_retry_missing_session test_stage1_handoff -v
```

These cover real Git reference races/bundles, bounded provider retries,
session recovery, refusal of changed/stale receipts and the independent-reader
handoff. Q93's normal dry run passed with the repaired tools. The saved receipt
matched the active worker and sandbox when this report was prepared.

Resume the existing sandbox and follow the current brief's role. Preserve the
split, statement-only `lem-trf-finite-horizontal-shriek-mate`, citations,
searches and first-reader report. Maintenance did not evaluate or approve the
mathematics. Complete the normal first-reader handoff and independent second
reading; rerun the ordinary no-push delivery after any input changes. Any new
content or citation finding still needs normal repair. Do not delete valid
sandbox material in response to the historical moving-baseline false positive.

Worker/maintenance records are under
`/home/ubuntu/weil-launcher-all/{run,maint}/Q93*`; the specific maintenance
directory is `Q93-lem-trf-weil-shriek-operator-fibres-1792197035`. The active
worker is allowed to finish normally. Provider errors may still occur; they
must remain recoverable infrastructure diagnoses, not permanent item bans.
