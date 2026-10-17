# D4 strict-henselization pointed evaluation: maintenance

## Cause and evidence

The ten counted failures at dispatcher key
`Sheaf.Paper.StrictHenselizationPointEvaluationPointed@` were temporary provider
failures. Each run ended with `ERROR: exceeded retry limit, last status: 429 Too
Many Requests` and no nonempty `last.txt`. The attempt suffixes were:

- `1792193076`, request `652fae28-a149-4325-875f-425423b6a500`;
- `1792195989`, request `90ca7c1a-29a9-43d0-a570-cd74e54ee9a1`;
- `1792196153`, request `fa58b54c-0dd0-4031-bf41-d92785d142ee`;
- `1792196183`, request `9df37023-663d-45cf-b175-dcb2ba666d8f`;
- `1792196229`, request `abee7cc6-e837-4b03-8f45-413c96125988`;
- `1792196280`, request `a383d9d1-a927-4563-a0a5-7811de623214`;
- `1792196368`, request `e44eecdc-336a-4019-9de1-4054293dbfc3`;
- `1792196407`, request `7574a038-a7d2-4790-9774-f3edb37433f6`;
- `1792196563`, request `7b7932de-aeff-4cd6-a9e4-509895e67f5d`;
- `1792196923`, request `bfb22a95-4c1d-46cd-b77b-6c844076f053`.

The launcher recorded D4's last failure at 2026-10-17 08:30:29 (+08), in a
cross-project burst of unrelated `NOANSWER` failures. The old dispatcher read
only the final-answer file, discarded the terminal provider error, and
re-dispatched into the same provider outage. This explains the ten failures;
they do not establish a problem with the theorem.

A second launcher/data mismatch explains the empty key suffix: the running
older dispatcher parses `branch head`, while this batch return used `head
55b353d39`. The newer dispatcher source already accepts both spellings, but the
running process predates that change.

## Repairs and validation

Concurrent launcher maintenance had already deployed the shared recovery fix
before this D4 change. `/home/ubuntu/.local/bin/codex` points to
`/home/ubuntu/weil-launcher-all/codex_retry.py`. It supervises exact dispatched
worker invocations, backs off temporary 429/concurrency failures, resumes the
same session when available, retains the original deadline and sandbox, and
emits a useful diagnostic if recovery is exhausted. New invocations use it
without restarting the dispatcher. The deployed entrypoint was checked and
reported `codex-cli 0.162.1` for ordinary version calls.

The authoritative shared launcher history is in the server project
`/home/ubuntu/weil-newtargets`: `a1a68055f2` adds provider recovery,
`a5ae0952c3` handles explicit resume calls, `0fa398c792` recovers missing saved
sessions, and `ecbefbec53` covers adaptive provider capacity. Related commit
`6fb280508f` preserves reader handoffs and transport diagnostics. These fixes
were verified, not overwritten by D4 maintenance.

Validation completed during this maintenance:

- Current server retry regressions: 18 tests passed.
- Current server provider-capacity regressions: 8 tests passed.
- Resume and retry regressions against the deployed local supervisor: 15 tests
  passed, using fake child CLIs and no provider requests.
- Python syntax checks passed for the deployed retry supervisor, dispatcher,
  and capacity helper.

D4 maintenance changes `coord/returns/D4.md`: normalize the existing returned
head to `branch head 55b353d39`, preserve all other entries, and add the provider
diagnosis and exact prerequisite handoff. The previous file is retained as
`coord/returns/D4.md.maint-D4-pointed-1792197030.bak`. This new report is retained
alongside its `.bak` snapshot. No failure count was cleared or used to stop
work. No process was stopped, and no Lean source or DAG node was changed by
maintenance, so no maintenance Lean compilation was needed.

## Next worker

Keep the existing sandbox at
`/home/ubuntu/weil-sandbox/D4/Sheaf.Paper.StrictHenselizationPointEvaluationPointed`.
The original delivery `55b353d396` used the pre-sync small-colimit interface.
The current theorem repair must use the current project API.

The upstream sync replaced the body of
`AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation` with `by sorry`.
E2 owns the prerequisite module `Sheaf.Paper.StrictHenselizationPointEvaluation`
and its active repair has passed a dry run at `c8fe3a4136` during this audit;
that dry run is not a landed commit. D4's retained proof needs the concrete
evaluation construction. Fetch current `sheaf-dag` and check the published
prerequisite before compiling and handing off D4's repair. E2's separately held
module belongs in E2's delivery; D4's attempted inclusion was correctly refused
by the forced-adaptation guard because the old module compiles with `sorry`.

Preserve the target statement and node audit. Compile each changed Lean module
individually with `tools/lean_file.sh` and the 60-second limit, then perform the
normal dry run and independent second-reader handoff. If the prerequisite is
still pending, retain the sandbox and name the dependency in the answer.
