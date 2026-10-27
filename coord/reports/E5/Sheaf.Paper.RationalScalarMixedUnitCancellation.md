## What changed

Fill five companion theorem proofs in Sheaf.Paper.RationalScalarMixedUnitCancellation,
without changing any existing declaration signature, data construction, public import,
or normalization. Add five proved private helpers for integral realization maps and
scalar multiplication of normalized tensor sections, and adjoint-comparison
associativity. A private import of all declarations
of Sheaf.Paper.CompletedAdicCoefficientDatum reuses its proved completedTensor_smul.
Update the owning node's proof text to describe the completed companion arguments;
the remaining proof plan and its dependencies are retained.

The unit precomposition proof uses the fraction formula at denominator one,
alpha_normalization, theta naturality, and the supplied mixed compatibility.
The local section proof applies ordinary.inv to ordinary_units and uses linearity
and the scalar-adjunction unit. Raw naturality is naturality of the actual composite
of whiskered theta, alpha and zeta on every raw morphism. The common tensor formula
uses the precomposition equations, zeta naturality, and cancellation in theta = s t⁻¹.
The pentagon identifies reduction normalization with the composite left-adjoint
comparison. The ordinary restriction comparisons are identity on sections, their
cocycle passes to derived categories by mapDerivedCategoryCompNatIso_cocycle,
and Mathlib's leftAdjointCompIso_assoc gives the required equality. Postcomposition
with the same zeta component preserves it. Add private proof imports of
Mathlib.CategoryTheory.Adjunction.CompositionIso and
WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle.

Validation: lcompile.py compiled the complete delivered module without errors or
warnings in 41.2 seconds, below the 60-second limit. The delivery tool performs the
required independent declaration and axiom checks.

## Proved and sorry left

Original holes: 12. Closed: 5. Added: 0. No split-off statements.

Closed declarations (namespace AlgebraicGeometry.Scheme):

- rationalMixedUnitPrecomposition_eq
- rationalMixedOrdinarySections
- rationalMixedRawNaturality
- rationalMixedCommonTensor
- rationalMixedPentagon

The seven original holes below remain unchanged, all attached to
lem-per-rational-scalar-mixed-unit-cancellation:

- rationalScalarMixedUnitCancellation
- rationalMixedGeometricComposition
- rationalMixedRawGeometricComposition
- rationalMixedGeometricIdentity
- rationalMixedCoefficientTower
- rationalMixedRawCoefficientTower
- rationalMixedCoefficientIdentity

## No longer needed

Remove the following redundant private proof imports:

- Sheaf.Paper.LocalizedOrdinaryPullbackNormalization
- Sheaf.Paper.QuotientCompletedCompositorUnit
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares

The completed companion proofs do not use their assertions. Their declarations
needed in the remaining proof plan are already accessible through the retained public
imports. No DAG node or module is withdrawn; these dependencies remain planned for
the seven original unproved obligations. No upstream declaration or source module is
removed. The unit route and all top-level tool-use approvals remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The companion section, naturality and common-tensor assertions admit categorical
proofs from the supplied normalized mixed comparison. They need no additional
K-flat representative comparison: that work belongs to constructing the comparison
in rationalScalarMixedUnitCancellation, which remains a separate original hole.
The right precomposition equation follows from the mixed record's compatibility
once the left equation is proved.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
