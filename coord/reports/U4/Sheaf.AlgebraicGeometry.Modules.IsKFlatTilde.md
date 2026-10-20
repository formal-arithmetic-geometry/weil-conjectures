## What changed

Retired `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde` in favor of
`WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde`, following the Hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. Replaced the imports in all three
live consumers: `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison` and
`Sheaf.AlgebraicGeometry.QCohTensorResolutionAffineModel`. Import visibility stays
the same. The official `isKFlat_tilde` returns `IsKFlatTensor`; it applies directly
at every existing call site because the old acyclic-tensor predicate unfolds to
the same proposition. Consumer signatures and mathematical arguments stay unchanged.
The last consumer also has pre-existing style warnings cleaned up. The affine
derived-pullback consumer uses `haveI`/`letI` for local instance proofs so Lean
inlines them during dependent category comparisons, following the optimization
documented in the official `DerivedPullbackCompositionLocalizedCounit` module.
The corresponding style linter is disabled with that explanation. Canonical
scheme-module instances have local priority, including their abelian, limit and
colimit instances; explicit reducibility annotations match the scheme/sheaf
wrappers while honoring transparency. The two private
comparison proofs and the base-change bridge application that require unfolding
retain the original settings locally.
These settings follow the official `DerivedPullbackCompositionLocalizedCounit`
module. No declaration signature changes.
The pullback counit uses the official module's narrower extraction from its
specification. A proved private wrapper converts the official K-flat conclusion
to the old predicate once for the two comparisons. No diagnostic profiler or
heartbeat settings remain.

Repointed `lem-pc-affine-tilde-kflat` to the official module, file and statement.
Listed the obsolete copy in `deleted.txt`. Change record:
`coord/changes/retire-isKFlatTilde-20261020.md`.

## Proved and sorry left

This is a retirement, with zero holes initially in the item and zero holes in
all three adapted consumers. Zero holes closed, zero holes added, zero split
off, zero holes left. The existing proof of `AlgebraicGeometry.isKFlat_tilde`
is supplied by the official twin. No proof is replaced by `sorry` and no data
construction changes. All three consumers compile through `lcompile.py`.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`, including its
private helpers. Removed every live source import of that copy and replaced it
with the official twin. The mathematical node and its proof dependencies remain
needed and are not pruned; its attachment now identifies the twin. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated this as a proof item despite its zero holes. The
current explicit RETIRE instruction resolves that mismatch. The inventory lists
thirteen consumers, but only the three named above remain in the current source
tree; the other ten are absent. Historical `created.item` references in two nodes
are provenance, not module attachments, and remain intact. No upstream file or
target statement was changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
