## What changed

Updated `lean/Sheaf/Paper/FiniteTorStability.lean` without changing any existing declaration
signature or definition body. Quotient restriction equality follows from the already proved
`compactSupportModuleRes_eq`. A proved private helper identifies intrinsic integral
constructibility with the legacy predicate using `sfDerivedComplete_iff_legacy`.
The residue-Tor and integral internal-Hom theorems then give integral finite-Tor equality,
Hom preservation and the canonical Hom reduction isomorphisms. Integral duality follows
by extracting the chosen dualizing tower's counit reduction isomorphisms and restricting
the existing integral Verdier anti-equivalence. The canonical Verdier reduction is the
composite of the integral Hom comparison with internal Hom applied to the dualizing
reduction. A proved generic product-map isomorphism helper avoids unfolding the coefficient
constructions during typeclass search.

Added private proof imports of `Sheaf.Paper.CompactSupportCoefficientTransition` and
`Sheaf.Paper.SfDerivedCompleteLegacyComparison`. Retained only private imports used by
these proofs or by declarations of this file. Updated the existing node's proof and
proof dependencies to record the normalization and predicate comparisons. No source-library
module, target statement, public import or existing definition was changed.
The four-hole version compiled without warnings in 51.1 seconds through `lcompile.py`
as a complete-file diagnostic. The preceding three-hole version compiled in 42.8 seconds.

## Proved and sorry left

Closed 4 of the item's original 15 holes, from existing dependency declarations:

- `sfStabilityQuotientRestrictionEquality` (node `thm-sf-ctf-stability`).
- `finiteTor_stability_integral_hom` (node `thm-sf-ctf-stability`).
- `finiteTor_stability_integral_verdier` (node `thm-sf-ctf-stability`).
- `finiteTor_stability_integral_verdier_reduction` (node `thm-sf-ctf-stability`).

Added zero holes and split off zero statements. The private predicate-comparison helper
and the generic isomorphism-composition helper are fully proved. The following 11 original theorem holes remain unchanged, each attached
to `thm-sf-ctf-stability`:

- `finiteTor_stability`.
- `finiteTor_stability_exceptional_verdier`.
- `finiteTor_stability_verdier_intrinsic`.
- `finiteTor_stability_constructible_adjunction`.
- `finiteTor_stability_origin`.
- `finiteTor_stability_quotients`.
- `finiteTor_stability_geometric_quotients`.
- `finiteTor_stability_integral_images`.
- `finiteTor_stability_integral_adjunction`.
- `finiteTor_stability_rational`.
- `finiteTor_stability_algebraicClosure`.

These proofs use existing named dependency theorems; they do not claim to eliminate
those dependency theorems' own holes.

## No longer needed

No node or module is withdrawn. Dependencies for the still-unproved finite, exceptional
and coefficient-passage clauses remain in the DAG. Removed the following unused private
imports from this module; future proofs can import a dependency when they actually use it:

- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `Sheaf.Algebra.Homology.DerivedTensor`.
- `Sheaf.CategoryTheory.RingedSitePerfectDuality`.
- `Sheaf.Algebra.Homology.SitePerfectTorWindow`.
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Paper.FiniteCoefficientFlatModel`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Paper.FiniteConstructibleHom`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`.
- `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`.
- `WeilConjectures.SixFunctors.Finite.Stalk`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.Paper.StratumAmbientHom`.
- `Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle`.
- `Sheaf.Paper.SfLocalizationAllStages`.
- `Sheaf.Paper.FiniteCtfTriangulated`.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`.
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`.
- `Sheaf.Paper.DirectImageTorAmplitude`.
- `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing`.
- `Sheaf.Paper.OpenExtensionFiniteTor`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.OpenComplementUnconditional`.
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`.
- `Sheaf.Paper.SmoothExceptionalPreservation`.
- `Sheaf.Paper.PurityGeneralAdmissibility`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.IntegralHomReduction`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.FiniteCoefficientHomChange`.
- `Sheaf.Paper.PurityAffineChartBounds`.
- `Sheaf.Paper.SfPreservationClass`.
- `Sheaf.SixFunctors.CoefQbarVerdier`.
- `Sheaf.SixFunctors.FiniteCoefficientVerdier`.
- `Sheaf.SixFunctors.RationalOperations`.
- `Sheaf.SixFunctors.RationalVerdier`.
- `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`.

The reviewer restored the private imports `Sheaf.Paper.FiniteTorAmplitudeSites` and
`Sheaf.Paper.CompactificationCoherence`: they are modules of nodes realized by the units
sk-def-sf-setting and sk-prop-sf-comp-coherence, which the still-unproved clauses (i)-(ii)
and (iv) use (coord/brief-stage3.md: a unit-route module stays imported).

## Where the brief, the DAG or earlier work was wrong

The current source exists and is byte-identical to the quarantined rework source; no
archive restoration or withdrawal is needed. The quotient-normalization theorem already
has a proved library lemma, so repeating the coefficient-ring induction is unnecessary.
The integral Hom dependency uses the legacy completeness predicate rather than the
intrinsic predicate of this item's statement; the proved augmented-tower comparison
bridges them without changing either definition. All existing statements and the unit's
route are preserved. No new nodes or change records are needed.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
