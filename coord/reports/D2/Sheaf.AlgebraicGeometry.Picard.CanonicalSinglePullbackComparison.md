## What changed

Restored the reworked module as a compatibility import of the adopted source
module `WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`.
The source module supplies the three original declarations and their complete
proof, while the compatibility import avoids redeclaring `derivedPullback` and
therefore fixes the duplicate-environment error recorded in `coord/rework.tsv`.
The delivered file compiles as a module and preserves the public names and
signatures used by the quarantined importers. The module-scoped option and
documentation update are recorded in
`coord/changes/D2-canonical-single-pullback-comparison.md`.

## Proved and sorry left

The adopted source implementation already proves
`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSinglePullbackMap`; this
compatibility module contains no `sorry` and adds no holes. There are zero
sorries in the delivered module.

## No longer needed

The quarantined implementation's public import of
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` and its duplicate local
copies of `canonicalTensorPullbackAdditive`, `canonicalSinglePullbackMap`, and
`isIso_canonicalSinglePullbackMap` are unnecessary. The adopted source module
exports the same interface and complete proof.

## Where the brief, the DAG or earlier work was wrong

The quarantined pre-sync file followed the old Sheaf derived-pullback
implementation. After the upstream sync, importing that file also imported the
adopted source implementation and failed because both declared
`AlgebraicGeometry.derivedPullback`. The DAG statement and proof plan remain
correct; only the module attachment needed the compatibility-import repair.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
