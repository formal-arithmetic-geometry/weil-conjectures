# B2 proper-adjoint worker: completed landing imports

The repeated `IntegralRestrictionClosed differs from committed source` failures
occur before Lean runs. The source is the completed proof landing
`20261022T051844-L-3458684`, with staged SHA-256
`78b430634f01f1261d091193ebd07ba5025860abb9b5ef3a9a77b0fad087bc69`.
Its private helper adds an exactness instance; no public theorem is changed.

`tools/landing.py` documents that the working tree is the merge candidate:
completed requests and their staged sources intentionally precede the global
build's commit. `tools/remote_compile_dependencies.py` required every missing
published import to equal Git HEAD, so this valid candidate could never reach
the compiler. Asking its owner to commit again misidentified the workflow.

The compiler resolver now accepts the latest completed request for a path when
its recorded digest, staged bytes and live source all agree. It compiles those
staged bytes only in the request's private overlay, retaining the normal
60-second per-file limit. Diagnostics identify the base commit and landing id.
Committed sources retain their existing path. Unrecorded edits, incomplete or
superseded landings, missing or corrupt staging, and deleted entries are refused.
This changes the worker compiler, not the landing or review tools.

Validation: all 13 tests in `tools/tests/test_remote_compile_dependencies.py`
pass, including the compiler-service test for a completed landing and its
provenance. The original tests still check dependency order, request precedence,
private caching, import parsing and error propagation. Six new cases cover the
merge-candidate workflow and its refusal conditions. No Lean source or DAG
record is changed by this repair; no published object is written.

Independent Lean validation uses `tools/lean_file.sh`, one file at a time at
60 seconds in the private group `B2-adjoint-maint-1792649565`.
`CompactificationCoherenceCocycle` compiled; `NonrationalCompositionSeed` reached
the 60-second limit. That is a separate dependency diagnostic, not a source
publication failure. It is left for the appropriate proof/rework worker; this
maintenance change does not claim a successful compilation or delivery of the
proper-adjoint item. The original quarantine and worker packet remain intact.
