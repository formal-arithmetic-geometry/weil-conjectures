## What changed

Replaced the proof of
`AlgebraicGeometry.ProEtale.RealizedTowerPurity.realized_tower_purity_transpose`
without changing its statement. The main module proves the tower Hom-transpose
identity directly from the definition of `SpTowerGamma.tensorMate`. It proves
reduction of the realized map by the reconstruction triangle, applies the pinned
counit reduction, descends equality through faithful simultaneous reduction, and
transfers to an arbitrary finite-Tor right adjoint using its counit-preserving
unique isomorphism. Naturality, invertibility and the entire-tower reduction are
also proved there. Projection naturality supplies the second displayed word.

`TowerPurityRealizedNormalization` states the remaining normalization step: the
finite coefficient/source normalizations and reduction of the projection word to
the explicit tower projection/counit word. It does not assert the integral
adjunct identity or the reduction of its left side. These are combined by real
Lean proofs in the item, rather than deduced from finite evaluations. The
normalization witnesses stay together so every comparison uses the same
realization and models.

The existing eighteen definitions were moved verbatim to
`TowerPurityRealizedData` and publicly re-exported by the original module. This
avoids the cycle from the normalization lemma back to definitions originally in
its consumer. Two new explicit definitions, `towerProjection` and `reduceWord`,
record whole-system composites; neither chooses data from an existence theorem.
No source-library file or target statement changes.

The proof treats the large completed tensor/pullback and realized-map definitions
as locally irreducible. The fixed nested existential statement needs a scoped
800000-heartbeat allowance for its elimination and reassembly; the remote
compile-time limit is unchanged.

## Proved and sorry left

Original holes: 1. Closed the body of
`AlgebraicGeometry.ProEtale.RealizedTowerPurity.realized_tower_purity_transpose`.
Its proof is complete from the remaining named normalization theorem and the
existing declarations. The main module and the data module have zero holes.

Added holes: 1, the public theorem
`AlgebraicGeometry.ProEtale.RealizedTowerPurity.realized_tower_purity_normalization`
in `Sheaf.Paper.TowerPurityRealizedNormalization`, node
`lem-pur-realized-tower-purity-normalization`. Its docstring supplies the source
and full proof in words. This is a decomposition, not a net reduction in holes:
1 original hole closed, 1 lower hole added, net 0.

The remaining theorem is strictly a part of the argument: it normalizes the
right projection word and the finite coefficient comparisons. The item proves
the tower transpose, reduction of the left adjunct, faithful descent, adjoint
transfer, naturality, invertibility and the whole-system component equation.
The lower theorem does not contain the original integral adjunct conclusion.

Validation: the main module compiled cleanly, without warnings, in 41.3 seconds
through `lcompile.py`. The data and normalization modules also compiled. Delivery
rechecks the packet after removal of the unused normalization proof imports.

## No longer needed

The following proof-only imports are removed from the item. They are not used
by the completed categorical proof or by the statement of the remaining lemma:

- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Paper.CofinalCoefficientProjectionCocone`
- `Sheaf.Paper.CofinalFiniteReductionConstructibility`
- `Sheaf.Paper.IntegralReconstructionComparisons`
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionComparison`
- `Sheaf.Paper.TwistedPullbackReductionTower`
- `Sheaf.SecSmoothPurity.ReductionCompatibilities`

The original public imports are supplied by the public data-module re-export;
their redundant direct imports are removed from the item:

- `Sheaf.Paper.PurityFiniteSetting`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.SmoothPurityCoefficientTowers`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
- `WeilConjectures.Compactification.RefinementCategory`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.IntegralAdjunctionBijection`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `Sheaf.Paper.SmoothPurityTowerGamma`
- `Sheaf.Paper.SmoothPurityMap`
- `Sheaf.Paper.CompactificationBProjectionReduction`
- `Sheaf.Paper.CompleteProjectionMateDescent`
- `Sheaf.Paper.CompletedUnitPullbackData`
- `Sheaf.Paper.AdicPurityObjects`
- `Sheaf.Paper.AdicPurityExceptionalReduction`
- `Sheaf.Paper.AdicPuritySourceReduction`
- `Sheaf.Paper.TwistedPullbackReductionData`
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`
- `Sheaf.SixFunctors.IntegralOperationShiftData`
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Mathlib.CategoryTheory.Limits.Shapes.Products`
- `Sheaf.Paper.ConstructibleExceptionalCompositorData`
- `Sheaf.Paper.AdicUnitTraceTensorCoordinates`

These dependencies remain in the normalization node's proof plan; its future
proof will import the declarations it uses. No whole module or existing DAG
dependency is withdrawn from the targets' route. The item's DAG
now records the actual combination proof, with normalization as its dependency;
the normalization node records the old coefficient/projection dependencies.
No unit statement or realized unit step is bypassed. No source-library
declaration is removed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan describes normalization of
several coefficient, reconstruction and projection comparisons together but has
no declared theorem giving their simultaneous normalized square. The delivery
isolates precisely that remaining calculation. Merely applying the finite
comparison equations would not justify integral equality; the item instead
uses the entire tower and faithfulness of simultaneous reduction.

The definitions needed by the new square originally lived in the consuming
module. Their unchanged extraction is required to express the reduction without
an import cycle. All existing public imports are preserved by re-export.

The edge checks for the new square are the unit, d=0, identity quotients, zero
objects and empty schemes: it asserts equality of the actual functorial words,
not cancellation by a scalar or a geometric nonemptiness assumption. The
inverse-projection square is required for every second-input arrow, including
the zero arrow, and is ordinary projection naturality. The normalization proof
must use the canonical diagonal orientation and augmentation comparisons, not
arbitrary endpoint isomorphisms.

## New nodes

`def-pur-realized-tower-purity-data` attaches the unchanged realized-map,
finite-normalization and projection-word definitions to
`Sheaf.Paper.TowerPurityRealizedData`, with the two new explicit system words.
There is no hollow definition or chosen witness.

`lem-pur-realized-tower-purity-normalization` is the single remaining proof
obligation in `Sheaf.Paper.TowerPurityRealizedNormalization`: normalized finite
comparisons, reduction of the projection word, and inverse-projection
naturality. It has the original chapter/unit provenance, full source proof and
search records. The original node is updated to the combination proof.

Change record: `coord/changes/D3-realized-tower-purity-data-extraction.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
