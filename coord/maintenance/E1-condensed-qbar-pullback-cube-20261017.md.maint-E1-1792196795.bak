# E1 cube maintenance, 2026-10-17

Item: `Sheaf.Paper.CondensedQbarPullbackCube`, stage 3.

The repeated empty `NOANSWER` results are terminal model-service HTTP 429 failures,
not rejected mathematical deliveries. Nine consecutive completed worker runs from
`1792190284` through `1792196711` had that error and no final-answer file when this
maintenance started; run `1792196800` then failed the same way. The dispatcher read
only `last.txt`, discarded the diagnostic, and launched fresh workers. Its first
maintenance run also ended with HTTP 429. The attempt inventory is archived below.

The running dispatcher started before the concurrent infrastructure repairs. Its
next CLI launches already use the new `codex_retry.py` entry point without a restart.
That supervisor preserves the exact session and original budget across temporary
provider errors, retains a terminal diagnostic, and checks for an existing final
answer before retrying. The underlying provider can still be unavailable; the E1
CLI errors alone do not establish its account-specific reason for rejecting calls.

During verification, a concurrent supervisor revision had lost the explicit
`--last` exclusion and the stdin-marker check in `resume_session`. Maintenance restored
both checks in the deployed launcher. The narrow patch, a runtime source snapshot,
and regression tests are in `tools/maintenance/20261017-E1-cube-recovery/`.
This prevents the recovery mechanism from accepting a shared last-session selector.
It does not change the model, concurrency settings, worker eligibility or mathematics.

The item-specific note is installed on the launcher at
`/home/ubuntu/weil-launcher/route-notes/Sheaf.Paper.CondensedQbarPullbackCube.md`,
and versioned at `tools/launcher/route-notes/Sheaf.Paper.CondensedQbarPullbackCube.md`.
The dispatcher reads it dynamically on the next author attempt. It directs the next
worker to retain the existing sandbox and start with the current delivery dry run.

The historical missing `OverSquare.olean` now exists on the launcher. The sandbox
report attributes the old tensor-instance mismatch to inherited compiled artifacts;
it has four changed Lean modules, change records and five proposed completed proofs.
Those claims still need whole-delivery validation and independent second reading.
Maintenance checked the unchanged server main-branch cube once with
`SHEAF_GROUP=MAINT_E1_CUBE_1792196795 SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh
lean/Sheaf/Paper/CondensedQbarPullbackCube.lean`; it timed out with exit 124.
That result neither certifies nor rejects the newer sandbox proof. The current item
worker is continuing its own compiler/delivery work and was not interrupted.

Validation: the selector regressions fail twice against the saved original and pass
all four tests against the installed file. Fourteen fake-CLI recovery tests and five
shared-admission tests also pass. No external model calls were made for these tests.
No Lean source, node binding, mathematical statement, failure counter, claim or
delivery branch was changed by this maintenance. No global build or process kill ran.

Existing edited files have `.bak` backups. The launcher backup for the guard repair is
`/home/ubuntu/weil-launcher-all/codex_retry.py.maint-E1-1792196795.bak`.
The new route note has adjacent backup snapshots. Archive snapshots are evidence;
they are not instructions to overwrite later infrastructure improvements.
