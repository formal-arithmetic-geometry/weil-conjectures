# CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence

## Reason

Source-encoding correction under step 5 of the worker brief. Stacks 00VI explicitly
excludes big sites. Stacks 03AZ proves the spectral sequence in that convention,
using enough injectives and derived functors. The previous Lean declaration
asserted more: an arbitrary large site and an independent coefficient/index universe
under HasExt alone. Its own docstring marked the realization step disputed.
The supported source statement is an essentially v-small site with v-small
coverings and v-small coefficients/Ext. Enough injectives now follows from the
proved Grothendieck-category theorem, rather than being a new hypothesis.

Sources: https://stacks.math.columbia.edu/tag/00VI and
https://stacks.math.columbia.edu/tag/03AZ.
This is a correction of a non-target interface, not a proof of the old generality.
No counterexample to the old generality is claimed. The prior repair required
preserving it while restricting CechGeneral; this delivery instead explicitly
proposes a source-convention correction of the primary node itself, with its
statement_change record and a CODEX review. The unit's injective-resolution,
column, total and spectral-sequence proof route is preserved.

## Old

```lean
theorem Sheaf.exists_cechToDerivedSpectralSequence [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{w},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X
```

## New

```lean
theorem Sheaf.exists_cechToDerivedSpectralSequence [EssentiallySmall.{v} C]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X
```

The other two theorem signatures and visibility remain identical. No definition
changes. No statement or definition in Challenge.lean changes. Thus this correction
does not reopen the meanings of the five Challenge targets. Module/declaration
layout is preserved. The declaration's docstring and module size notes now describe
the corrected statement. Proof imports supply the Grothendieck-category result,
the AB axioms for abelian groups and the enough-injectives instance. The redundant
plain import of CechResolutionDoubleComplex is removed (still publicly exposed by
the already imported column/total modules).

## Users

The source-only scan found 129 transitive downstream modules and no external code
application of exists_cechToDerivedSpectralSequence. Its only non-comment code
occurrence is its own declaration. Every downstream module is listed below;
no adaptation is delivered. The four direct importers are compiled unchanged
against the corrected sandbox module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CechH1Injective | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneral | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.Paper.BoundaryDerivationAlgebraicData | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.Paper.BoundaryDerivationSquareZero | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| TargetsCheck | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No application of the changed declaration; statements, definitions and proofs unchanged. |

The five DAG citers are individually recorded in statement_change.citers. They
use small scheme/open sites, so their mathematical statements still hold.

## Status

landed 20261013T072357-L-1122241 2026-10-13 (merge of deliver/M1/WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech)
