# Q04 def-trf-adic-system maintenance, 2026-10-18

Dispatcher key: `def-trf-adic-system@a7bc35ce6`. This is an operational handoff,
not a mathematical review or a resolution of the return on `a7bc35ce6fa9`.

## Cause

The five repair workers starting at 1792301123, 1792303864, 1792306599,
1792309325 and 1792312068 each exhausted approximately 45 minutes. None wrote
`last.txt`; their retry records still say `running`, recoveries 0, last_error
empty. Four logs contain the supervisor's `Stopped: 15` traceback; all five
dispatcher completion records give 45 minutes. These are deadline interruptions
during active compilation and Lean repair, not evidence of a provider empty
response. No HTTP 429 or gateway rejection was found in these attempts.

There are real source diagnostics as well as validation overhead. The latest
completed diagnostic, `scratchpad/abstract-comparisons-dry-run.log`, reports
an `isDefEq` heartbeat timeout, unconstrained `EssentiallySmall`/derived-change
universes and the consequent missing `adicRestrictionFrobenius`. The worker
subsequently saved explicit smallness universes and derived-descent endpoints.
Those later bytes are being checked; the older errors do not establish that
the retained packet still has the same faults.

The compiler treats all caller-supplied modules and their transitive side
importers as private. Those modules bypass its persistent cache, so each
invocation repeats the dependency closure before checking the item. The five
worker logs contain respectively 91, 153, 199, 235 and 275 private-overlay
progress lines across their checks. The packet includes low-level dependency
repairs (notably `FiniteFieldFiber`), so this overhead is substantial.

At 09:15 UTC on 2026-10-18, earlier `deliver2.py --no-push` processes 542380
and 587025 survived with PPID 1 and advancing logs. The current worker had
also started process 642337. These PIDs are observations, not process-control
instructions; verify current status and results. Maintenance did not stop them.

## Resume from the retained work

The sandbox is
`/home/ubuntu/weil-newtargets-stage2-sandbox/Q04/def-trf-adic-system`.

Reconcile these current check results with the source revision each compiled:

- `scratchpad/explicit-smallness-dry-run.log`;
- `scratchpad/explicit-descent-endpoints-dry-run.log`;
- the current worker log under
  `/home/ubuntu/weil-launcher-all/run/Q04/def-trf-adic-system.1792314800/`.

Use the completed result to select the next source repair or delivery step.
The original return remains applicable: recorded coefficient categories, the
chosen geometric fibre, completed-sheaf restriction, system morphisms and the
separate realization notion must all be retained. Keep the substantive saved
replacement and its dependency repairs. The older upstream duplicate-declaration
blocker was repaired by the previous maintenance and is not the current cause.
No new clean dry run or repaired delivery was established by this maintenance.

## Protected tool follow-up

The maintenance REPORT.md records the evidence and required owner changes:

- `dispatch_all.py`/worker supervision: durably distinguish deadline interruption
  from provider failure and reconcile in-flight validation or delivery results
  when resuming a saved packet. `NOANSWER: ` loses the actual phase and cause.
- `tools/nt_srv_compile.py` and
  `tools/launcher/nt_local_compile.py` (also used by the landing path): reuse
  successful private dependency artifacts only when the exact source, recursive
  import identities, compiler version and options match, preserving supplied
  overrides, isolation and both namespace checks. A repaired item must never
  resolve an older published dependency silently. Successful equivalent checks
  should remain identifiable across worker deadlines.

These protected tools were inspected, not edited. No concurrency cap, throttle,
admission limit, pause or failure-count cutoff was introduced. The existing
uncommitted changes in the two server compiler tools belong to another actor
and were left untouched. No Lean or DAG statement was changed by maintenance.
