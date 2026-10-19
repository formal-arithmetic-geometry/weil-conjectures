# Q25 maintenance: coefficient-system derived comparison

2026-10-16. Item: `lem-pur-coefficient-system-derived-comparison`, stage 2.

The repeated failures were a real prerequisite-module defect. The item has no Lean
delivery yet; its workers correctly isolated a failure importing the recorded
`thm-weil-pbc-site-comparison` module alone. The dispatcher's retry count is history,
not a dispatch limit, and was not reset or used to stop the item.

## Cause

`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` publicly imported
`ProEtaleFiniteModuleIntrinsicComparison`. That module imports `ProEtaleOperations`
and reaches `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
The derived comparison's private finite-level proof dependency reaches the older
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`. Both define
`AlgebraicGeometry.ProEtale.lowerStarComp` (and other names).

Compilation of the dependency itself passed, but a downstream plain import failed
when Lean loaded the conflicting declaration environments. Recompiling that same
source, as the former `lean.note` advised, could not fix it. Consumer-side import
reduction was exhausted: the worker's probe already imported just this module.

## Repair

Changed only the public coefficient import in
`lean/Sheaf/AlgebraicGeometry/ProEtaleSiteComparisonDerived.lean` to
`Sheaf.Paper.RefinementCoefficientRealization`, the module currently recorded for
the statement dependency `def-weil-pbc-proetale-modules`. It reexports the same
finite-module definitions and canonical coefficient realization, without importing
unrelated intrinsic module operations. All six declarations, their definitions,
signatures, docstrings, theorem proof and private proof imports are unchanged.

Updated only `lean.note` in
`dag/nodes/sec-proper-base-change/thm-weil-pbc-site-comparison.json` to replace the
ineffective rebuild instruction with this cause and repair. The item's mathematics,
statement, DAG dependencies and delivery status were not changed.

Both pre-edit files are saved beside their originals with suffix
`.maint-Q25-1792137141.bak`. This report is committed with the source and record
under `SHEAF_LEAD=L-only flock coord/.merge.lock`, using Bin Wu's required identity.
The maintenance workspace's `REPORT.md` records the resulting commit hash.

## Validation

All server compilation used `bash tools/lean_file.sh <one-file>` with its fixed
60-second per-file timeout, nice 19 and two threads. No global build was run and
no live-project source or artifact was written.

Before the edit, `lean/.sandbox/maint-Q25-1792137141/SiteComparisonDependency.lean`
reproduced the duplicate `lowerStarComp` import failure. The derived module itself
compiled in 1.6 seconds, while its importer failed in 2.8 seconds.

After the edit, the same sole-import probe, checking both the theorem and derived
adjunction, passed in 4.2 seconds. The prerequisite files compiled separately:
`ProEtaleFiniteModules` 5.1 seconds, `RefinementCoefficientRealization` 1.5 seconds,
and `ProEtaleSiteComparisonDerived` 1.8 seconds.

The worker's complete `scratchpad/Dependencies.lean` was copied to
`lean/.sandbox/maint-Q25-1792137141/Dependencies.lean` and also passed, in 4.2 seconds.
It combines the recorded restriction-of-scalars, unbounded derived category,
K-injectivity, derived change of rings, constant sheaf, ringed modules and site
comparison dependencies, and checks the relevant comparison declarations.
The probes are untracked diagnostic files. The normal launcher compile path is
checked after the server commit; the workspace report records that result.

## Next worker

Continue stage 2 for the original item. Import
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` normally; no replacement
dependency statement or new mathematics is needed for this repair. Read the current
server source with `scompile.py --source` if a checkout lags. Do not reintroduce the
intrinsic-comparison import into this module merely to force a rebuild. Continue
the normal per-file compile and delivery dry run for the item's own statement.

Proof dependencies need not be Lean statements merely to state the item. In
particular, the earlier NO-worker complaint about
`lem-pur-coefficient-evaluation-derived-left-adjoint` concerned a proof dependency,
not the Q25 prerequisite failure repaired here.
