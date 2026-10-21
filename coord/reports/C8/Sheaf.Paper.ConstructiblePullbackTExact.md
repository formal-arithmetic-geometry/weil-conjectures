## What changed

In `Sheaf.Paper.ConstructiblePullbackTExact`, reuse the comparison witnesses already
contained in `constructible_pullback_scalar_compatibility` to prove
`constructible_pullback_t_exact`. Move that theorem after its prerequisite.

Prove `constructible_pullback_point_fibre` from the pullback comparison and the
point-evaluation comparison witnesses already contained in
`constructible_point_scalar_compatibility`. Construct the natural cohomology
isomorphism by whiskering, composing, and inserting functor associators. Check its
component formula. Apply the two heart-factorization equalities to identify the
resulting object as a standard heart object, then use the positive and negative
homology-vanishing criteria. Move this theorem after its prerequisites. Every public
signature stays unchanged. The two point-comparison definitions now supply the
already intended target category explicitly to `f.cohomology`; this changes no
equation or predicate. No other definition body changes.

Keep the heavy functor definitions abstract locally while applying the proved generic
helper. Enable backward definitional equality and respect transparency, locally
prioritize the existing rational triangulation and division-ring torsion-free
instances, and cache the standard derived-module shift-additivity proof privately.
These elaboration settings and helpers export no changed attributes.

The complete item compiles without warnings through `lcompile.py` (52.9 seconds).
The explicit-category elaboration record is
`coord/changes/C8-constructible-point-comparison-elaboration.md`.

Update step 11 of `lem-a1-constructible-pullback-t-exact` and its proof-origin note to
record this reuse and the explicit composition argument. The other proof steps and
the unit route stay in place.

## Proved and sorry left

Closed two of the four existing holes:

- `WeilConjectures.constructible_pullback_t_exact`.
- `WeilConjectures.constructible_pullback_point_fibre`.

Two existing holes remain, both attached to
`lem-a1-constructible-pullback-t-exact`:

- `WeilConjectures.constructible_pullback_scalar_compatibility`.
- `WeilConjectures.constructible_point_scalar_compatibility`.

No holes or new public intermediate statements were added. Four proved private helpers
handle elementary functor composition, heart membership, homology vanishing, and
their combination; they have no postponed proof obligations. The first closed theorem is a
consequence of the existing stronger scalar-compatible statement. The second has
a complete composition and degree-zero proof from the existing comparison data.
These proofs continue to depend on the two listed unproved declarations.

## No longer needed

No module or DAG node is withdrawn. The dependencies of the two retained
scalar-compatibility proof plans are still needed. The following private imports
are unnecessary for the implemented proofs and existing declarations, and are removed:

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`.
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`.
- `Sheaf.Paper.CompletedPullbackTriangles`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Paper.PointProEtaleSectionsExact`.
- `Sheaf.Paper.PointSectionsScalarExtension`.
- `Sheaf.Paper.LocalizedTStructure`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.Algebra.Module.LocalizedModule.Exact`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.IntegralPullbackCompletedComparison`.
- `Sheaf.Paper.IntegralPullbackComposition`.

These import removals do not claim that the retained scalar proof plans can omit
the corresponding mathematics. The point-fibre
proof reuses the exact point-evaluation data already required by scalar compatibility,
so it adds no separate point-evaluation lemma or duplicated proof obligation.

## Where the brief, the DAG or earlier work was wrong

The original four independent holes repeated existence data: scalar compatibility
already quantified over the pullback comparisons and the point-evaluation comparisons.
Those existing witnesses suffice for the two non-scalar conclusions. No mathematical
statement is disputed or changed, and no unit step is bypassed.

Searches run through msearch: LeanFinder for canonical truncation/cohomology and
heart comparisons (eight generic results, no exact match); Loogle for
`Functor.IsTExact` (unrecognized short identifier, zero results); grep for pullback
t-exactness (zero results). Repository searches found the local comparison packages
and the existing Mathlib `DerivedCategory.isZero_of_isLE` and
`DerivedCategory.isZero_of_isGE` APIs used for concentration. No new node was needed.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
