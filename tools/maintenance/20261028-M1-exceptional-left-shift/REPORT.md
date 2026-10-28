# Maintenance: Sheaf.Paper.ExceptionalTransportLeftShift

The root cause was stale dependency artifacts in the compile service, not the
item's proof plan or a need to repeat its mathematics. The pipeline repair is
committed on the server as `f9fcd1cb1d7b70e7401c6cd55265c3bbbec0cc26`.

## Cause and evidence

The preserved stage-3 packet changes the existing `LeftRealization` definition
in `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` from a bare
isomorphism to a record retaining shift compatibility. Unchanged intermediate
sources must be elaborated against that representation. Their published
objects still contain uses of the previous isomorphism projection.

`tools/remote_compile_dependencies.py:missing_dependencies` seeded dependency
invalidation only with modules absent from publication. Replacing an existing
published module did not invalidate its published importers. Consequently the
official 15-file compile mixed the new data object with old intermediates,
including `ConstructibleExceptionalCoefficientConstructionData`, and failed at
`ConstructibleRingLeftRefinement.lean:78` with the kernel diagnostic
`Iso.hom (R.left c (RingStage.integral L))` applied to the new record.

The sandbox's unchanged validation objects could not cure this: the intentional
`lcompile.local_artifacts` filter excludes objects with absent or unchanged
sandbox sources. Removing that filter or manufacturing source changes would
hide the compiler defect. The worker's earlier all-source validation is retained
in `~/weil-launcher/compile-results/a4a78797b25355921a651354.txt`: 212 successful
module headers, maximum printed time 57.0 seconds. That is historical worker
evidence, distinct from maintenance validation below.

The dispatcher counted five completed BLOCKED answers. Later attempts reused
the completed failed compile `l1a8887234a1be3445bfe9186.last.json`. Its cache
dependency signature covered the published stamp and Lean source tree, but not
the compiler implementation, so a compiler-only repair also needed to expire
those diagnostics. The recovered HTTP 429 interruptions occurred after the
compiler result arrived; they were not this item's delivery failure. No provider
configuration was changed.

## Changes and backups

Server project: `/home/ubuntu/weil-conjectures-sheaf`.

- `tools/remote_compile_dependencies.py` now seeds invalidation from existing
  caller replacements as well as new modules, and rebuilds the affected
  transitive importers within the request's import closure. Both published
  import traces and current source headers identify affected objects. Sources
  must still match a committed snapshot or a verified completed landing. The
  published build is never modified.
- `tools/tests/test_remote_compile_dependencies.py` adds six regressions for
  existing definition changes, caller artifacts, transitive imports, missing
  Lake traces, old recorded imports, source trust, and service ordering/cache
  reuse (some cases share one test).
- `tools/maintenance/20261028-M1-exceptional-left-shift/` archives the launcher
  cache patch and its separate regression test.

These four files were committed with the exact staged set printed, under
`SHEAF_LEAD=L-only flock coord/.merge.lock`, using the requested author identity.
Existing server files have adjacent `.M1-1793168654.bak` copies.

Launcher machine: `/home/ubuntu/weil-launcher/lcompile.py` now includes the
committed compiler helper and service blobs in its cache dependency signature,
alongside the Lean tree. Its backup is
`/home/ubuntu/weil-launcher/lcompile.py.M1-1793168654.bak`; its patch is in the
server commit above. The ordinary shared-clone refresh has deployed the server
compiler repair to the local compile service too. The integrity monitor first
restored the launcher edit at 14:30:43 dispatcher time. Its documented
`check.py --accept F...` procedure explicitly permits legitimate maintainer
edits, so the fix was reinstalled and registered through that procedure. Before
registration, adjacent `.M1-1793168654.bak` copies were saved for both
`/home/ubuntu/weil-launcher-all/integrity/manifest.json` and
`/home/ubuntu/weil-launcher-all/integrity/pristine/weil-launcher/lcompile.py`.
The guard remains active; only the `lcompile.py` entry and pristine copy changed.

Working copies and original `.bak` files are in this maintenance directory.
No item Lean source, node, proof dependency, change record, or statement was
changed. No protected launcher/landing/review tool was edited. No concurrency
cap, admission rule, pause, or throttle was introduced; no unrelated process was
stopped.

## Validation

- Six new dependency cases reproduce the missing invalidation; the original
  implementation failed the first five before the sixth was added.
- All 37 dependency regressions pass locally and on the server, including the
  existing relocation and source-provenance tests.
- `test_lcompile_compiler_cache.py` fails against the original launcher and
  passes against the installed repair. It makes real git commits in an isolated
  fixture: compiler changes alter the dependency signature while the Lean tree
  is unchanged; unrelated metadata changes leave the signature unchanged.
- A read-only dependency-plan check on all 15 packet sources schedules 198
  private dependency recompiles, including the previously stale intermediate.
  The plan is recorded in `packet-dependency-plan.json`.
- A supported recompilation of the preserved 15-file packet completed:
  `python3 /home/ubuntu/weil-launcher/lcompile.py --all
  /home/ubuntu/weil-sandbox/M1/Sheaf.Paper.ExceptionalTransportLeftShift`.
  Its output is `packet-recompile.log`; the stable compiler result is
  `/home/ubuntu/weil-launcher/compile-results/b44f03daa09e072346379d69.txt`.
  The former stale-object error is replaced by a real source diagnostic in
  `ExceptionalRingTransportCorePostFunctorData.lean:127,237`: these old-source
  constructions require explicit projections of `LeftRealization.toIso`.
  A concurrent normal worker delivery retry reported the same fresh-source
  error. This establishes that the compiler is now recompiling the affected
  intermediate, rather than hiding its source errors behind an old object.
  Files compile sequentially; no `lake build` was run.
- An isolated Lean reproducer of the exact `R.left` shift hypothesis PASSES
  against freshly rebuilt, unchanged construction and assembly intermediates
  (exit 0; requested files 1.9 and 6.3 seconds). Its stable result
  is `/home/ubuntu/weil-launcher/compile-results/037fcf4d6a3a87d62ad229f3.txt`
  and its log is `smoke-assembly-recompile.log`. An initial smoke check imported
  only ConstructionData and lacked `constructionInclusionShift`; the corrected
  check imports AssemblyData, where that definition lives.

## Next worker

The preserved sandbox is
`/home/ubuntu/weil-sandbox/M1/Sheaf.Paper.ExceptionalTransportLeftShift`.
Keep the packet and associated records. A concurrently active normal worker
expanded it from 15 to 17 Lean files while this maintenance validation ran,
adding the real `.toIso` adaptations exposed by the fresh compiler in
`ExceptionalRingTransportCorePostFunctorData` and `ExceptionalRingTransportCorePostData`.
Those edits were not made by this maintenance session and have not been
independently certified here. The earlier 212-source worker result is not proof
that the current unchanged committed consumers all elaborate against this
packet: fresh compilation has now found a counterexample. Do not add unchanged source
copies or artificial `.toIso` edits solely to make an artifact survive filtering.
The compiler now supplies the necessary unchanged intermediates privately.

Use the normal
`python3 /home/ubuntu/weil-launcher/deliver3.py M1
Sheaf.Paper.ExceptionalTransportLeftShift` path. The dependency rebuild can take
time; repeated identical compile commands attach to the same running request.
Read the stable result before starting another compile. Review and landing of
the mathematical packet remain the normal pipeline's responsibility.

The pipeline repair is validated. The full mathematical packet has not passed
its new fresh-source checks yet; its active worker must finish the exposed
consumer adaptations and normal delivery. This maintenance session did not
claim a successful delivery or land the packet.
