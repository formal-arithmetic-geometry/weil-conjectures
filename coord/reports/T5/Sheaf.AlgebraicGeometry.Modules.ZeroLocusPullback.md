## What changed

Proved `AlgebraicGeometry.Scheme.Modules.Hom.comap_zeroLocus_tensorPullback`
in `Sheaf.AlgebraicGeometry.Modules.ZeroLocusPullback`, with its signature unchanged.
Convert invertibility using the existing bridge, compare tensor and abstract pullback by
uniqueness of left adjoints, apply the proved source `Hom.comap_zeroLocus`, and transport
its conclusion using naturality and `Hom.zeroLocus_eq_of_arrowIso`.
The original docstring describes a valid longer proof and is preserved.
Updated the item's DAG proof to record this reuse and transport.
No definitions, public imports, instances, source-library declarations or consumers change.

Server single-file compilation passed in 3.3 seconds, with no warnings.
Searches used LeanFinder, LeanSearch, Loogle, the launcher's Mathlib grep and repository rg.
Mathlib supplies adjunction uniqueness but only set-level zero-locus pullback results;
the two required scheme-module zero-locus theorems are already proved in the source library.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.Hom.comap_zeroLocus_tensorPullback`
(node `lem-pc-zero-scheme-pullback`).
Zero holes remain in the item. Zero holes added; zero split off.
This is a complete proof, not a decomposition.

## No longer needed

Removed the private proof imports:
- `Sheaf.AlgebraicGeometry.Modules.PullbackLocalCoefficient`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`.

The tensor-specific node `lem-pc-zero-scheme-pullback-local-coefficient` and its module
`Sheaf.AlgebraicGeometry.Modules.PullbackLocalCoefficient` are no longer needed by this item:
naturality transports the whole morphism, so its coefficients need not be transported separately.
No module is withdrawn, and other consumers may still need it.

The affine ideal extension, local ideal and common-generator nodes remain dependencies of the
reused source proof; their declarations and source modules are retained. The affine extension
module is imported transitively by the source library, so removal of its direct import does
not assert that it leaves the targets' closure. The full abstract-pullback coefficient node
is recorded as part of the source theorem's existing proof. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's tensor-specific local calculation was unnecessary:
the complete abstract-pullback theorem and invariance under isomorphic arrows already exist.
The distinction between tensor and abstract pullback is respected by an actual natural
isomorphism, rather than treating the two constructions as definitionally equal.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
