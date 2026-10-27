## What changed

Filled the coefficient-ring and intrinsic-realization infrastructure proofs in
`lean/Sheaf/SixFunctors/FiniteDualizing.lean`. Quotient identities use the existing
ideal-quotient API. The regular-unit comparison is constructed through module
sheafification, with invertibility checked on underlying additive sheaves and
uniqueness checked on the constant generator. Scalar restriction is compared with
realization through the fully faithful scalar-restriction functor, and the
comparison is verified on the prescribed section units. The sequential coefficient
tower is identified with the diagram of actual quotient homomorphisms. Exactness
is reflected by the additive-sheaf forgetful functor. The derived normalization
and right adjoint then follow by transport.

All existing public signatures, definitions, attributes, public imports, and
existing docstrings are unchanged. Added only proved private helpers. Removed the
unused private imports listed below. No source-library module was changed.
The main geometric theorem is left for a subsequent round; its existing named
statement and proof plan remain intact.

Validation: compiled the item remotely with `lcompile.py`. No new theorem holes,
definition holes, axioms, nodes, or forced adaptations were introduced.

## Proved and sorry left

Original hole count: 9. Closed: 8. Added: 0. Remaining in this module: 1.

Closed declarations (namespace `WeilConjectures`):

- `WeilConjectures.finiteDualizingQuotient_id`.
- `WeilConjectures.finiteDualizingQuotient_comp`.
- `WeilConjectures.finiteDualizingIntrinsicUnit_existsUnique`.
- `WeilConjectures.finiteDualizingRestriction_existsUnique`.
- `WeilConjectures.finiteDualizingRestriction_eq`.
- `WeilConjectures.finiteDualizingGenericRestriction_exact`.
- `WeilConjectures.finiteDualizingIntrinsicRestriction_existsUnique`.
- `WeilConjectures.finiteDualizingRestriction_isRightAdjoint`.

The sole remaining `sorry` is
`WeilConjectures.finiteDualizingCoefficientComparisons`
(node `lem-coef-finite-dualizing`). It is the existing geometric comparison theorem,
including its quotient identities and intrinsic transport. Its proof and statement
are unchanged. This is partial progress on the original module, not a decomposition
of the geometric theorem into additional assumed statements.

## No longer needed

Removed these private imports (49 lines, 48 distinct modules; the
`LowerShriekLeftAdjoint` import was duplicated):

- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
- `Sheaf.Paper.WeilVerdierPreservationStrata`.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`.
- `Sheaf.CategoryTheory.AdjointMate`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`.
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`.
- `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`.
- `Sheaf.Paper.ConnectedTateLineEndomorphisms`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `WeilConjectures.SixFunctors.Finite.Exact`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.Paper.FiniteClosedShriek`.
- `Sheaf.CategoryTheory.FullyFaithfulCounitDescent`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`.
- `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport`.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`.
- `Sheaf.Paper.SfCommonStageWeilCohomology`.
- `Sheaf.SixFunctors.CompactCoefficientComposition`.
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`.

These imports are unnecessary to elaborate the existing interfaces and the proofs
completed here. Some are already available through public dependencies. This does
not withdraw any module or DAG node: the main geometric proof is still unfinished,
and its affine, closed, open, quotient-mate, and site-mate dependencies remain
recorded in the DAG. No unit route is bypassed, and no global module pruning is
claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The supporting proofs can be completed
using the existing quotient and sheafification APIs without adding intermediate
public statements. The geometric proof dependencies remain necessary for the
unfinished main theorem; no change to its route is claimed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
