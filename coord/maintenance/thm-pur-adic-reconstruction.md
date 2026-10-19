# N0 thm-pur-adic-reconstruction maintenance, 2026-10-18

Item key: `thm-pur-adic-reconstruction@4a9d51a17`.

## Current recovery: 1792310957

The repaired thirteen-module packet has now been DELIVERED, at
`ea5f51a2e0b832eb8854050db3c7ea226ee4e58a`, on
`deliver/N0/thm-pur-adic-reconstruction`. This is a delivery for independent
stage-2 review, not an approval of its mathematics or a landing.

The immediately preceding worker (run 1792308236) completed its prescribed dry
run: `scratchpad/resume-final/final-dry.log` ends with
`OK (dry run): commit 785e81b0a6 passes the preflight and compiles; nothing pushed`.
Maintenance compared all thirteen sandbox Lean sources and thirteen node JSON
files with that commit; all 26 match byte for byte. The report subsequently
recorded the successful validation. The named exposed
`AdicPurityFiniteTensorIsoType` used verbatim by the comparison field was the
worker's successful compiler repair; the obsolete source/twist timeout is no
longer a current diagnostic for these bytes.

The worker then ran the prescribed delivery wrapper. At its 45-minute deadline
the worker's parent exited with `Stopped: 15` and no final answer, but delivery
PID 3514388 survived with PPID 1. Its `final-push.log` continued advancing after
the dispatcher counted `NOANSWER` and started a new repair worker. Maintenance
observed that existing process instead of starting another check or killing it.
It finished all thirteen modules and preflight, printed
`DELIVERED thm-pur-adic-reconstruction at ea5f51a2e0`, and the server delivery ref
was independently verified. The new repair worker had meanwhile started another
`--no-push` invocation. No delivery outcome should be inferred from the killed
parent alone.

Next worker on this item:

1. Read the current server delivery ref and the end of
   `scratchpad/resume-final/final-push.log` first. The repaired packet is already
   submitted. Retain this packet and use the next independent review of
   `ea5f51a2e0` to select any further repair. The original return below applies
   to `4a9d51a1754e`, not to the newly delivered head.
2. The actual source/target, finite smooth-purity arrow, canonical normalization,
   coherent tower morphism and exact reduction identity remain mandatory.
   Maintenance changed no Lean or DAG statement and made no mathematical verdict.
3. A successful unchanged saved dry run is completed work. Resume the actual
   unfinished delivery step; if an already-started wrapper has a final result,
   reconcile that result with the server ref before choosing another action.
   The delivery wrapper still performs all its normal compile/preflight checks.
4. Old OrdinaryFiniteP1Arrows missing-artifact and DerivedPullbackTensorHom
   confirmation failures were real in run 1792305680. Later complete dry-run and
   delivery success supersede them for this packet. Diagnose any new failure
   from its current log rather than treating those older errors as current.

Protected tooling follow-up (REPORT.md in the maintenance working directory has
full evidence; these tools were not changed):

- `dispatch_all.py` reap/start: stage-2 deadline interruption becomes
  `NOANSWER: `, losing the cause and completed dry-run/delivery progress.
  Its saved-packet prompt unconditionally requests another dry run even when
  the identical packet has passed and its delivery is still executing.
  Preserve the actual phase, packet identity and wrapper result, and reconcile
  an already-pushed delivery ref before instructing another repair.
- `codex_retry.py`/worker supervision: the killed parent's retry record remains
  `running`, recoveries=0, last_error empty, while a delivery subprocess survives
  and can push. Record interruption and child delivery identity/result durably;
  an absent parent answer is not a provider error and is not a delivery result.
- `tools/nt_srv_compile.py` and landing compilation repeat successful private,
  preliminary, sandbox and library passes. Preserve the namespace checks while
  reusing only artifacts validated against the same sources/imports/options.

No provider rejection was found. No dispatcher/admission/landing tool, dispatch
state, worker process, concurrency setting, Lean source or DAG statement was
changed by this maintenance. Backups of the two edited server records have the
suffix `.bak.1792310957`; the maintenance commit includes only those records.

## Historical diagnosis: 1792297493 (superseded by recovery above)

Item key: `thm-pur-adic-reconstruction@4a9d51a17`. This note supplements the
independent return of head `4a9d51a1754e`; it does not approve that head or the
unsubmitted repair.

The five repair runs starting at 1792283892, 1792286601, 1792289327, 1792292045,
and 1792294782 all ran for about 45 minutes. Each log ends with `Stopped: 15`,
each lacks `last.txt`, and each retry record has recoveries=0, last_error="".
These are deadline interruptions during active work, not evidence of a provider
empty response. No provider rejection was found in those logs.

The saved repair has thirteen modules, eleven new helper nodes, a repaired
exceptional-image dependency, and the replacement reconstruction statement.
Keep this work. The original rejected head quantifies over arbitrary endpoints;
it is not a useful starting point for a fresh implementation.

Concrete remaining failure: the server repeatedly reaches a 60-second compile
timeout in `Sheaf.Paper.AdicPuritySourceReduction`, after earlier repairs of
`AdicPurityFiniteTensor` and `ExceptionalDerivedSiteRealization`. The comparison
specialization/endpoint checks are expensive. Root-comparison compilation also
occasionally reaches the limit. This is not yet a compiling delivery.

Next worker:

1. Read the retained report and the newest scratch logs before changing code.
   `scratchpad/source-model-full.log` reaches source reduction; the later
   `scratchpad/generic-source-dry.log` includes a root-comparison timeout during
   confirmation. Read the newest result rather than restarting all searches.
2. Keep the actual source/target, finite `smoothPurityMap`, normalization data,
   transition/coherent-lift conditions, and exact reduction equation required by
   the original return. The mathematical statement is not being relaxed.
3. Profile a private diagnostic copy of the failing module. Check expensive
   exposed definitions and definitional equality at the concrete specialization.
   Explicit result types and `@[no_expose]` with characterizing lemmas are
   available techniques; neither permits replacing canonical data with an
   arbitrary isomorphism. Existing examples are
   `Sheaf/Paper/PointFibreDerivedTensorScalar.lean` and
   `PointFibreDerivedTensorBasic.lean` in the shared project. Keep a backup of
   every file changed and keep each Lean invocation within 60 seconds.
4. The compiler currently recompiles supplied helpers as private overlays and
   then again as preliminary/sandbox/library sources. One saved ten-file run
   spent 611.8 seconds on successful compiles before its timeout; 293.8 seconds
   were private-overlay/preliminary passes in addition to sandbox/library
   checks. This is a tool efficiency problem, not a reason to repeat an
   unchanged whole-packet compile concurrently with another one. Wait for an
   already-started check's result, then use its concrete diagnostic.
5. Resume the prescribed wrapper dry run after repairing the diagnostic, then
   complete the author self-check and delivery. A killed worker's missing
   answer is not a successful dry run or a delivered repair.

Protected tooling follow-up (not changed by maintenance):

- `codex_retry.py` writes a stopped-worker diagnostic only when last_error is
  nonempty. On SIGTERM with active work and no provider error, it can leave the
  record "running" and no final file; a second SIGTERM can interrupt child
  cleanup. Record a deadline/interruption outcome without inventing a provider
  error or changing dispatch eligibility.
- `dispatch_all.py` only preserves its explicit TIMEOUT note for stage 3;
  stage-2 deadline exits therefore become `NOANSWER: `. Preserve a specific
  deadline reason and the latest compiler diagnostic for stage 2 as well.
- `tools/nt_srv_compile.py` serves landing plans as well as worker compilation.
  Reuse private outputs or order sandbox/library checking to avoid extra
  preliminary/private passes, while preserving both namespace checks and the
  caller-source override isolation. This is protected landing tooling and was
  not patched. A timeout confirmation also repeats expensive successful work.

No provider/admission settings, concurrency limits, dispatcher state, protected
tools, Lean sources, or DAG statements were changed by this maintenance.
