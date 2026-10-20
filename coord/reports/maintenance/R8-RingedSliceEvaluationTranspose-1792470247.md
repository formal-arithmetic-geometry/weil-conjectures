# R8 RingedSliceEvaluationTranspose maintenance, 2026-10-20

Item: `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose@new`, stage 3,
project `/home/ubuntu/weil-conjectures-sheaf`. Dispatcher recorded 22 tries.

## Cause and disposition

The current failure is a source/publication mismatch after the retirement of
`Sheaf.Algebra.Homology.HomComplex`, before the worker's proof elaborates.
Migration `b20d1112cfef08092468e6822be1b8a9b381fa94`, committed at
2026-10-20 09:46:04 +08, deleted the old module and rewrote its consumers to
`WeilConjectures.Algebra.Homology.HomComplex`. Both modules declare
`CategoryTheory.homComplexFunctor`. The published DerivedInternalHom dependency
closure still loads the old owner, so importing the upstream module alongside it
fails with a duplicate declaration.

The publication itself is not shown to be internally inconsistent. Its recorded
commit, `c0b7c0c3e0196e22606d2593c864ffaf4c2697cd`, published at
2026-10-19T23:01:37Z (07:01:37 +08), predates this migration. Its
`DerivedInternalHom.lean` and `CoefficientHomRepresentativeEvaluation.lean`
import the old Sheaf module. The buildloop's latest recorded in-progress snapshot,
`0d5526d52bd6abe57f6831e3c80880890a1ee2cb`, also contains those old imports and
the old module. A successful publication of that snapshot would not include
the HomComplex migration.

The audit found no open landing request covering the HomComplex deletion,
DerivedInternalHom, or CoefficientHomRepresentativeEvaluation, and no inflight
landing. This describes the observed state, not a claim that an automatic later
snapshot cannot register the migration. Earlier global builds were red on
FormalFunctionsStalk; subsequent global-build repair is already in progress.

**Not repaired by this maintenance run.** The durable fix belongs to the
migration/landing/publication path. The task expressly excludes editing landing
tools and forbids running a global `lake build`; the required owner change is
specified below. Rewriting the item's mathematics or selectively replacing
published artifacts would not establish a coherent verified environment.

## Fresh server verification

All checks used `SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`, one file at a time,
with no group mirror and no worker `.lbuild` artifacts:

| Probe | Result |
| --- | --- |
| `DerivedOnly.lean`: DerivedInternalHomOfUniverses alone | Pass, 51.3 s |
| `UpstreamOnly.lean`: upstream HomComplex alone | Pass, 5.5 s |
| `PublishedHomImports.lean`: both imports below | Duplicate declaration, 21.8 s |

```lean
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
```

The diagnostic is:
`import WeilConjectures.Algebra.Homology.HomComplex failed, environment already contains 'CategoryTheory.homComplexFunctor' from Sheaf.Algebra.Homology.HomComplex`.

The three source probes and their `.bak` copies are retained under
`lean/.sandbox/maintenance/R8-RingedSliceEvaluationTranspose-1792470247/`.
Local evidence includes the compiler output and an audit of actual imports in
the published commit, running-build snapshot, and current HEAD.

## Required landing/publication owner action

1. Register and verify the complete HomComplex retirement as a coherent
   migration, including the deletion and every affected consumer. Ensure the
   actual build candidate contains it; merely finishing the pre-migration build
   or changing `published.json` cannot fix this failure. Inspect migration
   `b20d1112cf` and its closure, rather than recompiling only the item.
2. Correct migration/snapshot bookkeeping if it omits or splits that closure,
   then publish matching verified artifacts through the normal owner workflow.
   Relevant paths are `tools/build.py` (`record_unrecorded`, `_snapshot`,
   `publish`), `tools/landing.py`, and the owning migration/landing caller.
   This is a requested owner investigation/change, not permission for a worker
   to edit those protected tools or fabricate verification records.
3. Check imports in the actual published commit and rerun the two-import probe.
   It must pass before the item can be validated against the migrated library.
   Cover source retirement versus an older published dependency closure in the
   owning workflow's regression checks. Preserve uninterrupted dispatch;
   introduce no concurrency control, throttle, admission limit, or pause.

## Changes and next worker

This incident note is the only tracked server change. No existing source, node,
worker packet, claim, return, dispatcher state, configuration, compiler tool,
landing tool, or published artifact was changed. The note and all new probe
sources have `.bak` copies. No global build ran and no process was signalled.
The note is committed under `coord/.merge.lock` with `SHEAF_LEAD=L-only` and
the required Bin Wu identity; its path's git log identifies the commit.

Retain `/home/ubuntu/weil-sandbox/R8/Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`.
Its seven-file packet is unaccepted work. The retained report says the original
transpose theorem and compatibility proofs are closed, with one named hole,
`CategoryTheory.ringedSlice_normalized_exists`. Maintenance did not revalidate
those proof bodies. The latest continuation's initial delivery dry run stopped
at the early split-off timing gate before compilation; its direct import and
unchanged-source probes independently reproduced the environment failure.
Do not describe that early gate as a successful delivery validation.

After a publication containing this migration, start with the brief's normal
`deliver3.py R8 Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose --no-push`,
check the import probe, and repair any actual packet diagnostics. Compile Lean
files individually with the 60-second limit. Do not reset failure counters,
alter the split-off policy, restore duplicate declarations, or treat the
remaining construction hole as solved by this environment diagnosis.

Earlier attempts also ended with provider HTTP 429 errors and a 600-second
temporary-worktree checkout timeout. Provider failures are external and not
ours to fix; no provider recovery or provider-setting changes were attempted.
The checkout failure is recorded in the earlier maintenance report
`R8-Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose-1792460041/REPORT.md`
on the launcher and belongs to protected `sharedrepo.py`. This run stops with
the current publication failure documented; it does not claim either older
failure was repaired.
