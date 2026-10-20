## What changed

Restored `lean/Sheaf/AlgebraicGeometry/LocallyFreeTensorSingle.lean` from the
quarantine path recorded in `coord/rework.tsv`. Redirected the proof-only
`import all` from the adopted source module to
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
where the scheduled sync moved the proved private helper
`AlgebraicGeometry.ProEtale.locallyFinitelyPresented_of_isZero`.
The public imports, declaration signatures, finite-free calculation, cover descent,
and original proof remain unchanged. Both uses of the relocated helper are retained:
the empty finite sum and the homology outside degree zero.

## Proved and sorry left

This is a zero-hole compilation repair. The restored declaration
`AlgebraicGeometry.ProEtale.CondensedRing.locallyFree_tensor_single` has a complete
proof. Holes before: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No statements are split off and no definitions are changed.

## No longer needed

Removed the obsolete proof-only
`import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`;
the ordinary public import of that source module stays. Its former private helper
is now imported from the matching `Sheaf.UpstreamExtra` module. No mathematical
nodes or modules are pruned: all existing DAG dependencies and the unit route stay.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly identifies the helper as unknown after the scheduled
source sync. Its definition and complete proof already exist under `Sheaf.UpstreamExtra`;
the existing ordinary public import did not make that private declaration visible.
The zero-rank and nonzero-degree cases therefore need the relocated `import all`.
No false statement, missing mathematical lemma, or DAG correction was found.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
