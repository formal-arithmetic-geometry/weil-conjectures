# AlgebraicGeometry.ProEtale.CondensedRing.brownCompactificationRefinementMap

## Reason

The explicit duplicate definition triggers expensive definitional equality checking when
compared with the canonical compactification refinement component. The original map is
Rp_* of the same open-refinement map, the same inverse derived compositor, and equality
transport along the same structural triangle. The only difference is that the canonical
component writes the last transport as `(eqToIso (congrArg κ e)).hom.app M`, whereas the
duplicate writes `eqToHom (congrArg (fun q ↦ (κ q).obj M) e)`. These are equal by equality
induction on e (or Mathlib eqToHom_app). Reuse the existing canonical construction directly.
No object, morphism, hypothesis or normalization changes. No new data is selected.

## Old

```lean
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ r K) ≫
    (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    eqToHom (congrArg
      (fun q ↦ (lowerStar Λ q).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K))
      r.hom.hom.hom_g)
```

## New

```lean
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  compactificationRefinementComponent Λ r K
```

## Users

`tools/downstream.py --uses brownCompactificationRefinementMap` finds only the item's
own theorem (two occurrences); no downstream file unfolds or references this map.
The full downstream import audit lists the following modules. Their signatures and
mathematical meanings are unchanged: the canonical map is identical by equality induction.
The unchanged direct importer MateOpenRestriction compiles against the changed module
in a scratch overlay (58.1 seconds); all other users see its unchanged public interface. Target signatures remain untouched; definition review
checks the canonical map's equal meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BrownExceptionalAdjoint | H2 | Definition reuses the identical canonical component; theorem proof filled. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.AdmissibleVerdierExchange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.AffineCounitScalar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.AffineSpaceRationalInduction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.ArithmeticRoots | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.DualityPullback | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeCompactComposition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeCompactScalar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteFreeScalarProjection | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteTorStability | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.GeometricComparisonData | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.GeometricOperations | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.GlobalVerdierDuality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.MateOpenRestriction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.OpenExceptionalScalarLocality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.OpenProEtaleCounitScalar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.OrderedTateScalarNormalization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.ProperExceptionalRestriction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.ProperProductCounitTranspose | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.QbarPerverseSubcategories | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.QbarPerverseSupportCondition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalExceptionalRestriction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalHomScalarTranspose | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalP1AmbientComposites | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalP1Triangle | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalP1UnitCounit | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalRestrictionGlue | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalTensorSymmetry | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RawChartScalarCounitPasting | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RelativeProductInputDomains | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.RestrictionLocal | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.ScalarExchangeConstituents | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.SfBidualityClass | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.SitePerfectRationalBidual | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.TateTwistedProjection | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.TensorAdjunctionExchange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.VerdierCoefficientRealization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.VerdierExchange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.FiniteExceptional | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralDualizing | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.IntegralVerdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.RationalOperations | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SixFunctors.RationalVerdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.SmoothPurity.NormalizedWitness | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Targets.AffineSpaceRationalLine | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.Targets.SmoothPurityQbar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | Identical canonical map and public theorem meaning; no source change. |
| TargetsCheck | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.PoincareDuality.Verdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.SmoothPurity.Defs | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.Statement | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Additivity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Basic | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.BorelMoore | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.CompactCohomology | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.CompactPullback | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Correspondence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.CorrespondencePair | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.CurvePieces | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Dualizing | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FibreCoherence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FibreModel | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FixedPoint | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FixedPointScheme | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Frobenius | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.GenericQuotient | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.HomologyUnit | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.KunnethVerdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.LocalTerm | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.LocalTermLocality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Main | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ModelExtension | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.OpenSquare | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.PointNormalization | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Product | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ProperCompatibility | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ProperCurve | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ProperPushforward | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.PullbackFamily | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.RelativeFrobenius | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Stalk | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.Statement | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.SupportedPairing | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.TraceClass | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.WeilBaseChange | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.TraceFormula.WeilTrace | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilSheaf.Curve | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilSheaf.LFunction | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.Rationality | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Identical canonical map and public theorem meaning; no source change. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not adapted | Identical canonical map and public theorem meaning; no source change. |

## Status

landed 20261025T011021-L-3634522 2026-10-25 (merge of deliver/H2/Sheaf.Paper.BrownExceptionalAdjoint)
