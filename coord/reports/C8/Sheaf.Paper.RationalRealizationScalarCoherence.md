## What changed

Completed `AlgebraicGeometry.Scheme.rationalRealizationScalarMixedComp` in
`Sheaf.Paper.RationalRealizationScalarCoherence` from the already stated normalized
mixed-composition equation. Added a proved computation-counit theorem in the new module
`Sheaf.Paper.RationalPullbackFlatComputationCounit`, and a private proved helper for
uniqueness of the ambient geometric compositor. Moved the existing private
pullback Hom-extensionality helper before its new use; its statement and proof are unchanged.

The compositor uniqueness argument first identifies ordinary maps using tensor-unit
generators and the canonical site compositor. On flat-term K-flat representatives the
direct pullback computation counit is invertible; the supplied and canonical normalization
equations then determine the ambient comparison. Naturality along a resolution extends
this equality to all derived objects. After identifying the three scalar comparison
records with their canonical forms, inversion of `rationalMixedGeometricComposition`
gives the required equation for the supplied comparisons.

The item privately imports the computation-counit module, the flat-resolution theorem,
and the comparison of site and monoidal tensor functors. The computation-counit module
privately imports the algebraic inverse-image presentation, left exactness and the
ringed-topos K-flat pullback theorem. Updated the item's proof plan and dependencies.
The counit helper was moved into its own module after profiling the completed proof;
it is fully proved and introduces no hole.
All existing public signatures, definitions and public imports are unchanged.
The standard derived-category localization instance is locally marked irreducible to
avoid expanding its construction during comparisons; its global attributes are unchanged.

Validated both modules with `lcompile.py --all`; both compiled successfully within
the per-file limit. All profiling commands and options were removed before delivery.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.rationalRealizationScalarMixedComp`
(node `lem-per-rational-realization-scalar-coherence`).

No holes remain in the item. No holes were added, and no unproved statements were split off. The new theorem
`AlgebraicGeometry.Scheme.rationalPullComplexCounit_isIso_of_flatTerms`
(node `lem-per-rational-pullback-flat-computation-counit`) is also fully proved.
The proof uses existing dependency declarations; this does not assert those dependencies
are themselves axiom-free yet.

## No longer needed

None. Every existing import and declared proof dependency remains used by the module.
No module, node, declaration or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous proof plan correctly identified the remaining task as uniqueness of arbitrary
normalized geometric compositors. That step is now proved. Computation counits cannot be
cancelled on arbitrary cochain complexes: the proof restricts the cancellation to flat-term
K-flat resolutions and then transports the equality by naturality. No mathematical
statement or definition needed correction. The unit route is retained.

## New nodes

`lem-per-rational-pullback-flat-computation-counit`, in
`Sheaf.Paper.RationalPullbackFlatComputationCounit`, isolates the invertibility of the
rational pullback computation counit on flat-term K-flat complexes. Its proof uses the
existing algebraic inverse-image presentation, left exactness, K-flat pullback, and
scalar-extension computation declarations. It is strictly a computation step of
normalized compositor uniqueness, and is proved in this delivery. The separate module
separates the expensive computation proof from the coherence assembly. The statement
also covers the zero complex and empty schemes; the coefficient map need not be
invertible or flat, because scalar extension is computed on a K-flat input.
No change record is needed: all
existing public statements and definitions are preserved.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
