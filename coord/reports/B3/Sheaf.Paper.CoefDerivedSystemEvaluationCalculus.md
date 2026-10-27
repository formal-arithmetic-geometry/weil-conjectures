## What changed

Completed nine existing proof bodies in `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`.
The ordinary quotient maps are constructed by the recorded scalar adjunction, and their
restriction naturality is checked explicitly. The mapping-limit projections are fixed
by the universal right-derived comparison and their K-injective normalization.

The prescribed scalar-derived pair keeps the actual coefficient extension, its counit
and both recorded adjunctions. Its tensor comparison is fixed by the ordinary scalar-unit
formula. K-flat preservation at a finite level uses an explicit acyclic lift, followed
by exact evaluation and the ordinary tensor-evaluation comparison.

The ordinary quotient component now projects the constructed natural mate
`coefficientQuotientNatTrans`; its definition unfolds to the original adjunction
formula. The finite quotient's existence and derived-existence witnesses have their
previously inferred types written explicitly. Local irreducibility and explicit types
avoid repeated unfolding of these large constructions. The finite-reduction model,
finite-quotient model, sequence-normalization isomorphism and finite-quotient Hom
comparison are also kept locally irreducible after construction. A section-local
instance selection avoids the generic semilinear abelian/derived wrappers, and the
standard derived-category instance returns to normal transparency before the large
calculus records. The section restores both generic instances at its end. The records
and their six tensor-model fields remain unchanged. No mathematical assertion or
chosen object changes.

## Proved and sorry left

Closed nine of the eleven original holes:

- `coefficientAbTowers_haveKInjectives`
- `coefficientMappingProjection_exists`
- `coefficientRestrictionComp`
- `coefficientOrdinaryQuotient_exists`
- `coefficientScalarTensorIso_exists`
- `coefficientTensorModelPreservation`
- `coefficientFiniteQuotientExtension_obj`
- `coefficientFiniteQuotientCounit_isIso`
- `coefficientSectionsLimitIso_exists`

Two original holes remain, both attached to
`lem-coef-derived-system-evaluation-calculus`:

- `coefficientEvaluationTensorIso_exists`
- `coefficientDerivedSystemEvaluationCalculus`

All four modules compiled without warnings within the 60-second per-file limit.
With these local transparency and instance settings, a fresh check of the actual item
file on the project server passed in 50.0 seconds.

No holes added; no statements split off. The three new helper modules have zero holes.
The acyclic-lift proof uses the existing named ordinary evaluation-tensor theorem; its
remaining original hole is included in the count above.

## No longer needed

No library modules or DAG nodes withdrawn. The final calculus assembly is unfinished,
so its stated dependencies and the unit route are retained.

The following private imports were removed from the item because none of its retained
proofs uses their declarations. This does not withdraw their nodes from the unfinished
calculus route:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.CategoryTheory.ClosedAdjunctionComparison`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.TensorParameterComposition`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`

The experimental item imports of `ScalarHomOrdinaryTensorComparison`,
`ScalarHomTensorCoherence`, and `SemilinearSystemsExistence` are also omitted.
`CoefficientActualScalarDerivedPair` needs only its two public statement imports;
its experimental proof imports were removed. Scratch work is outside the delivery's
Lean tree.

## Where the brief, the DAG or earlier work was wrong

The HomComplex owner mismatch in the route note no longer prevents import loading.
A fresh import-only check of the item environment passed.

The available semilinear evaluation K-flat theorem assumes flat terms, whereas
`coefficientTensorModelPreservation` requires arbitrary K-flat complexes. The stronger
argument constructs a right extension of every acyclic finite test complex, using
restriction of scalars above the chosen level and zero below it. Its acyclicity is
componentwise. This avoids an unjustified flat-term hypothesis.

The earlier report of ten completed bodies did not certify the current combined file.
The retained full tensor-evaluation proof still exceeds the 60-second file limit and
is not part of this partial delivery. The delivery counts only proofs checked together;
the remaining theorem bodies stay exactly `by sorry`, with their existing source and
proof plan. No proof was moved to a separate file to evade the limit.

## New nodes

`lem-coef-actual-scalar-derived-pair` supplies the proved constructor for a prescribed
scalar-derived pair and its actual coefficient specialization. All object data are
specified functors; no arbitrary object is selected from a mere existence assertion.

`lem-coef-prescribed-scalar-tensor-comparison` specializes simultaneous scalar tensor
models to that prescribed pair, retains the pure-generator normalization, and proves
uniqueness and K-flat preservation. It introduces no holes.

`lem-coef-semilinear-evaluation-acyclic-lift` proves the explicit right-extension
construction used to test arbitrary K-flat evaluation, including level zero and the
zero complex. It introduces no holes.

Change records: `coord/changes/B3-coefficient-quotient-component-annotation.md` and
`coord/changes/B3-coefficient-derived-existence-annotation.md`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
