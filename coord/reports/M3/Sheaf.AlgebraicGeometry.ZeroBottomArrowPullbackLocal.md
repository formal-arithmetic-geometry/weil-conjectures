## What changed

Restored `Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal` from its quarantined source and
retained the complete proof of `AlgebraicGeometry.Scheme.zeroBottomArrow_pullback_local`.
See change record `coord/changes/ZeroBottomArrowPullbackLocal.md`. Changed the public proof import from the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`
to `WeilConjectures.AlgebraicGeometry.DerivedPullback`, which exposes the scheme and derived
category declarations used by the public theorem signature. The proof compiles together with
the existing `Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare` dependency.

## Proved and sorry left

Closed the only theorem hole, `AlgebraicGeometry.Scheme.zeroBottomArrow_pullback_local`.
No `sorry` remains in the delivered module.

## No longer needed

None. The proof uses the affine chain model and bottom-free-chain pullback square declared in
its DAG proof dependencies, as well as the derived-pullback source declarations required by
the public signature.

## Where the brief, the DAG or earlier work was wrong

The quarantined module's `public import Sheaf.AlgebraicGeometry.DerivedPullback` referred to a
withdrawn empty module. Because the theorem signature is public, this left `Scheme` and
`HasDerivedCategory` unavailable to importers. The source-derived-pullback public import is
required; the theorem statement and DAG route are unchanged.

## New nodes

None.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
