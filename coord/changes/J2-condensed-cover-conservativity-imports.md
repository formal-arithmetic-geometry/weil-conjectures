# AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative

## Reason

Remove unused statement and proof imports after proving covering conservativity from the published
localization theorem. The static interface check requires a record for removing public imports and
adding the local ZeroObject scope. All existing declaration signatures, universes and visibility
are unchanged; no definition or target meaning changes. Namespace/scoped openings are local
elaboration context. Both direct importers use a plain import of this module, so its former
reexports do not propagate through them to their own importers.

## Old

```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

open scoped CategoryTheory.Obj

theorem condensed_cover_restriction_conservative
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (f : K ⟶ L),
      IsIso f ↔ ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      (∀ i : 𝒰.I₀,
        IsZero ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) →
      IsZero K)
```

## New

```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

open scoped CategoryTheory.Obj ZeroObject

theorem condensed_cover_restriction_conservative
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage X) :
    (∀ (K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (f : K ⟶ L),
      IsIso f ↔ ∀ i : 𝒰.I₀,
        IsIso ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.map f)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)),
      (∀ i : 𝒰.I₀,
        IsZero ((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory.obj K)) →
      IsZero K)
```

## Users

The prescribed downstream scan lists 240 transitive importers, all recorded below.
Only CondensedLisseProEtaleLocality and MateOpenRestriction import the item directly.
The first explicitly imports each of the four removed public imports itself; the second
uses the unchanged conservativity theorem and published condensed-module interfaces.
Unchanged copies of both direct importers compiled against the proved module in the
sandbox scratchpad: CondensedLisseProEtaleLocality in 15.0 seconds and MateOpenRestriction
in 30.7 seconds. No consumer source is included in this delivery.
For further transitive users there is no export change: both direct imports are proof-only.
The declaration-name scan finds only the item and MateOpenRestriction as textual users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | J2 | Single hole proved; theorem signature unchanged; unused exports removed. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | R1 | Direct importer; independently imports all four removed modules; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | J7 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | S9 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Direct importer; uses the same theorem and published module API; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | X2 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| TargetsCheck | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.Statement | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in shared snapshot | Indirect importer; unchanged public interfaces; no adaptation. |

## Status

landed 20261019T192751-L-1865355 2026-10-19 (merge of deliver/J2/Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative)
