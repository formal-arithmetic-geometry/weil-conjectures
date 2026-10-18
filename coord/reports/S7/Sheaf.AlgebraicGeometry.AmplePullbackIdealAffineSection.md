## What changed

Filled both proofs in `Sheaf.AlgebraicGeometry.AmplePullbackIdealAffineSection`.
The pullback helper transports the ideal section through the canonical left-adjoint
comparison and tensor-power isomorphisms. The main theorem combines the ideal section
and an ample affine section using tensor-section identities, then transports the result
to `f^*(L^n)`. The import of `WeilConjectures.AlgebraicGeometry.AmpleIso` is used for
`tensorPow_iso` and `nonvanishingLocus_iso` after the upstream sync made these helpers
available there.

## Proved and sorry left

Closed `pullback_ideal_section` and
`exists_ample_pullback_ideal_affine_section`. No `sorry` remains in the delivered module;
no new holes were added. The module compiles cleanly; the delivery probe checks the
axioms of its declarations.

## No longer needed

No proof-dependency nodes are pruned: all five proof steps are used. Removed the retired
`Sheaf.AlgebraicGeometry.AmpleIso` import and the duplicate ordinary upstream
`AmpleIso` import, using one `import all WeilConjectures.AlgebraicGeometry.AmpleIso`
instead. Also removed the retired `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`
import and redundant direct imports of `WeilConjectures.AlgebraicGeometry.TensorPullback`
and `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; their declarations remain
available from the retained imports. Removed
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`: this proof uses the
existing scheme-module tensor API, with no independent-universe tensor construction.
These removals eliminate redundant import edges,
not mathematical proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The return report correctly identified the failures after the upstream sync. The helpers previously
provided by `Sheaf.AlgebraicGeometry.AmpleIso` are now private declarations exposed by
`WeilConjectures.AlgebraicGeometry.AmpleIso` (imported with `import all`). The proof was
adapted to that current location; theorem statements are unchanged.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
