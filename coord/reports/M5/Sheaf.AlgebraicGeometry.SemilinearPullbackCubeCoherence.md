## What changed

Proved `AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG_cube` without changing
its statement. The proof adapts the already proved private `ordinary_coherence`
calculation from `Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence` locally.
The direct-image section calculation uses the proved `site_pasting`,
`restriction_pasting` and `mate_transport` helpers from
`Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence`, through a proof-only
`import all`. Mathlib's `Adjunction.leftAdjointCompIso_assoc` then gives
associativity for exactly the prescribed ordinary pullback compositors.

The remaining proof inverts associativity, adds equality transport for named
composites, normalizes six paths to one total scheme morphism, and cancels the
invertible face comparisons. The six-path calculation adapts the existing proved
private `pullbackSquare_cube` argument from
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCube`; that module is
not imported, and no declarations in the adopted source tree are changed.

Only the item module and its own DAG proof are changed. All added definitions are
explicit composites of existing isomorphisms. All private helper theorems are proved.
The existing public import and theorem signature are unchanged.

Validation: the final item compiled through `lcompile.py` in 14.5 seconds, with
no warnings or errors. A source check confirms zero sorry tokens, unchanged
public theorem signature, no new modules in the import closure, and no Lean
lines over 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG_cube`, node
`lem-sf-semilinear-pullback-cube-coherence`.

Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in the item, and none is
split off. The only added import was already in the item's transitive import
closure, so it introduces no unrelated holed modules. This does not assert that
every theorem underlying the existing operations is free of sorry.

## No longer needed

No baseline imports were removed, and no modules are withdrawn. All four original
DAG proof dependencies remain needed. The already proved strict-tower section and
mate helpers are recorded as an additional proof dependency.

The final proof avoids importing `SemilinearCompositorCoherence`: although its
ordinary associativity helper is proved, importing that module also introduces
unrelated `VaryingRingClopenSectionEvaluation` and
`VaryingRingOrdinaryClopenEvaluation` holes into this item's import closure.
The section and adjoint calculation is therefore reproduced locally using only
existing dependencies. No global pruning claim is made for these modules.

No exact-derived localization, proper/open alpha calculation, cartesianness,
openness, or properness is used. The result remains valid for arbitrary commutative
cubes, including identity maps and empty schemes.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid. Ordinary associativity and the six-path cube
calculation had already been proved separately in the library for the same
compositors and for another pullback theory, respectively. Their local adaptations
close the cube without splitting the obligation again. The node now records the
specific section helpers and explicit six-path cancellation argument.
No mathematical statement or definition is repaired or disputed.

The local proof commands are documented in
`coord/changes/M5-semilinear-pullback-cube-proof-commands.md`.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
