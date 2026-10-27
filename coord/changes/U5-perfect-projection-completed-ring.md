# AlgebraicGeometry.Scheme.PerfectProjection.ring

## Reason

The completed ring is repeatedly expanded during inference of tensor, limit and
derived-category structure. Make its existing abbreviation an ordinary definition
with the identical body. Both backward-unification transparency options are set to
false locally in the item where explicit conversion to existing coefficient objects
is needed. Its type and mathematical value are unchanged, by reflexivity; this
introduces no new construction, hypothesis, scalar action or completed category.

## Old

```lean
abbrev ring (T : Scheme.{u}) := adicLisseCompletedRing T d.ideal
```

## New

```lean
def ring (T : Scheme.{u}) := adicLisseCompletedRing T d.ideal
```

## Users

The `tools/downstream.py Sheaf.Paper.PerfectProjectionFormula --uses
AlgebraicGeometry.Scheme.PerfectProjection.ring` search returns 128 textual matches.
Each matching source was scanned for the namespace, a qualified reference or an open
of `PerfectProjection`. Only the item and `QuotientPullbackCompositorNormalization`
use this ring declaration. All other matches are distinct ring fields, local names,
ring tactics or prose. The normalization module already disables backward
transparency restrictions and its coefficient ring equations have the identical
value. No statement is weakened, strengthened or changed mathematically.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | P9 | Unrelated ring name or prose; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | X7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.CategoryTheory.LatticeRestrictionCupComparison | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.BoundedFlatTensorContinuity | B2 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ClosedTestUnitEvaluation | Z6 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.CoefficientScalarTensorRealization | D7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.CompletedFrameGenericComparison | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.FiniteFreeDualChainComparison | E5 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.FiniteScalarLocalModelComplete | X9 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | C9 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | J7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpSequentialContinuity | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | K5 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | H1 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | H3 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalDerivedClosedLocalization | F7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalDirectImageLaxRealization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalScalarProjectionMate | K1 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalScalarPullbackNormalization | K2 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | K3 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | M2 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.OpenInternalKFlatMateNormalization | F9 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.PerfectProjectionFormula | U5 | Identical completed ring value and type; local inference optimized. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | G7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ProfiniteFreeSliceDerivedHom | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.QlbarBoundedTensorColimit | N2 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | P7 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.QuotientPullbackCompositorNormalization | unclaimed | Uses the identical completed ring; existing transparency settings permit conversion. No adaptation. |
| Sheaf.Paper.QuotientSectionTensorNormalization | N4 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SectionOplaxTotalComparison | E3 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | J9 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | F2 | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.TameInertiaContinuousKoszul | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.TameInertiaScalarMate | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | T5 | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Unrelated ring name or prose; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | T7 | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unrelated ring name or prose; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unrelated ring name or prose; no adaptation. |

The ring used through the targets is definitionally identical. Independent review
can check the unchanged body and all actual consumer signatures. No target text or
mathematical interpretation changes.

## Status

landed 20261024T191427-L-349376 2026-10-24 (merge of deliver/U5/Sheaf.Paper.PerfectProjectionFormula)
