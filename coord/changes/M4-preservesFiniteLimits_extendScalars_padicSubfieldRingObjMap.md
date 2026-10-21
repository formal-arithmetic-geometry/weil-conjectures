# AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap

## Reason

Replace the original sorry body with a proof. The stage-3 preflight classifies changes
to these instance bodies as changes visible to importers and requires this record.
The instance result is a proposition: the existing signature is verbatim unchanged,
and proof irrelevance ensures that replacing its proof changes no consumer statement,
definition or computation. No consumer adaptation is needed. No target meaning changes.

## Old

```lean
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) :=
  sorry
```

## New

```lean
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj E)) := IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1}
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj E)) :=
    fun J ↦ HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
  obtain ⟨e⟩ := point_finiteFree.{u} ℓ h
  let n := @Module.finrank E F inferInstance inferInstance
    (Module.compHom F (IntermediateField.inclusion h).toRingHom)
  let e' : (∐ fun _ : ULift.{u + 1} (Fin n) ↦
      Mod.regular (Profinite.continuousMapRingObj E)) ≅
      (Mod.comap (Profinite.padicSubfieldRingObjMap ℓ h)).obj
        (Mod.regular (Profinite.continuousMapRingObj F)) :=
    Sigma.reindex Equiv.ulift
      (fun _ : Fin n ↦ Mod.regular (Profinite.continuousMapRingObj E)) ≪≫
        (biproduct.isoCoproduct _).symm ≪≫ e.symm
  obtain ⟨b, hb, hflat, hunit⟩ := scheme_basis_from_point _ _
    (Profinite.padicSubfieldRingObjMap ℓ h) (ULift.{u + 1} (Fin n)) e'
  exact hflat X
```

## Users

The required `tools/downstream.py <module> --uses <declaration>` audit found only
the item itself as a textual use (the other occurrences are in comments).
Since instances also have implicit consumers, the table conservatively includes all
133 transitive importing modules reported by that audit. Current claim records
were read to identify holders. None of these modules is edited. The signatures
remain identical, so no statement becomes stronger, weaker or different.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.LfpTensorSingle` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.BoundedConstructibleBaseChange` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.BoundedExchangeAmbient` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientFiniteDescentLisse` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientFiniteDescentSections` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientHeartClosure` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientHeartCommonStratification` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientHeartLisseRestriction` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CoefficientHeartTriangulated` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CompletedCondensedCoefficients` | claimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedCoefficientFamilyHomStage` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedCoefficientHomStage` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedCompactSupportProjection` | claimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFiniteFamilyHomDescent` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFiniteLocalSubmodules` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationMatrices` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedFpHomStage` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLocalCoefficientAdjoints` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLocalModelGluing` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLocallyClosedExtensionTower` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedOverlapFactorTranspose` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedPointCoefficients` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedPointDiscreteConstantComparison` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedPointSupertrace` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.CondensedZlReduction` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ConstantToContinuousScalarFlat` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ContinuousAlgClConstructibleTor` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ContinuousAlgClLocalFree` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ContinuousIntegralPullComposition` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.DerivedNakayamaResolution` | claimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FiniteConstantModelResolution` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FiniteDiscreteRestrictionEncoding` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FiniteEtaleLocallyFreeModels` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FormalClosedSupportDerived` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.FormalClosedSupportSheaves` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralConstantModelHeartClosure` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralMatrixKernelLocallyFree` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralModelSurjectiveClosedReflection` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.LisseFiniteCoefficientModel` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.LisseFiniteHomLift` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.OpenExtensionConstantModelConstructible` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.ProperUnboundedWindowBounded` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Paper.TAdmissibleCoefficientModels` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.SixFunctors.BrownHypothesesAmbient` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.Topology.ProfiniteCondensedRing` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | unclaimed | Proof only; statement and meaning unchanged. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | claimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | unclaimed | Proof only; statement and meaning unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | unclaimed | Proof only; statement and meaning unchanged. |

## Status

landed 20261021T061527-L-1786233 2026-10-21 (merge of deliver/M4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
