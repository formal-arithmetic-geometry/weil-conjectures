# CochainComplex.IsAcyclicTensorKFlat and CochainComplex.IsKFlatResolution

## Reason

The listed retirement item duplicates the complete implementation already adopted in
WeilConjectures.Algebra.Homology.KFlat. A text comparison after renaming the source's two
predicates finds only copyright and documentation differences: all tensor-Hom helpers,
tensor localization, zero-morphism instances and predicate data are identical.
Use that implementation directly. The source lacks the two legacy names used downstream,
so retain their existing import path as a minimal compatibility module.

This is a definition consolidation, not a no-op or rebase. The module shrinks from
375 lines to 50 and its two definitions become aliases of the adopted predicates.
The adopted source files are untouched. No module is withdrawn.

## Old

```lean
def IsAcyclicTensorKFlat
    (K : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    Prop :=
  letI := SheafOfModules.monoidalCategory R
  ∀ F : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ,
    F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic

def IsKFlatResolution
    {K G : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  QuasiIso f ∧ K.IsAcyclicTensorKFlat
```

The original module also copied the source's private tensor-Hom helpers and the public
SheafOfModules.preservesZeroMorphisms_curriedTensor and
SheafOfModules.preservesZeroMorphisms_curriedTensor_obj instances.

## New

```lean
public import WeilConjectures.Algebra.Homology.KFlat

def IsAcyclicTensorKFlat
    (K : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    Prop :=
  IsKFlatTensor K

def IsKFlatResolution
    {K G : CochainComplex
      (SheafOfModules.{max u v} ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  IsKFlatTensorResolution f
```

The public tensor instances are re-exported from the source with the same names,
types and instance attributes. The two legacy predicates remain semireducible defs:
ConstantCompletionEquivalence, ProjectionMateExact and four pro-etale/coefficient
coherence consumers mark IsAcyclicTensorKFlat locally irreducible. Changing it to an
abbrev would break those existing commands. The retained defs share the source data
and preserve exactly the original reducibility interface.

Unfolding either predicate gives exactly the old proposition, with the same site,
coefficient and complex universes. No assumption or existential choice is added.
Empty sites, zero rings, zero complexes and acyclic complexes are included by the
same universally quantified formula. Neither target statements nor unit steps change.
The definition change reopens statement review for any target that uses this interface;
its meaning is unchanged by definitional equality.
the compilation probe verifies the expanded formulas, and the canonical DAG attachment
remains Sheaf.Algebra.Homology.KFlatIndependentCoefficients.

## Users

Both tools/downstream.py --uses scans and the direct-import scan were read. The table
lists their union. No consumer source is changed: import paths, declaration names,
instance attributes, semireducibility and expanded types are preserved. The source
implementation is definitionally identical after the two predicate renamings, so no
consumer statement becomes stronger, weaker or different. Historical quarantined
consumers retain their preserved imports and need no restoration change for this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AcyclicKFlatCyclesFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.AcyclicKFlatTensor | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.ChangeOfRingsKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedChangeOfRings | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedTensor | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.DiagramKFlatReplacements | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.FiniteFilteredFlatSheafResolution | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlat | B4 | Consolidated with the source; retains both legacy defs. |
| Sheaf.Algebra.Homology.KFlatClosure | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatCoefficientUniverse | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatIndependentCoefficients | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatRHomCurrying | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatResolutionGeneral | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatStalkCriterion | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatTelescopeClosure | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatTensorProduct | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatTensorQuasiIso | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KFlatTotalTensorModel | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.KInjectiveHomComplex | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.NilpotentDerivedUpperBound | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.OpenRestrictionKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingBoundedProjectiveExtension | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingedInternalHomExactRestriction | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationModels | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SiteDerivedTensorDescent | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SplitFlatFilteredSheafModels | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SplitPerfectTensorKInjective | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.StalkKFlatTensorHomology | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonFlatPullback | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedHomPushforwardKFlatModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedPullbackConeSquareTransposition | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedTensorComplexCohomologyVanishes | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DerivedTensorStalkVanishing | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.EtaleTensorCokernelFlat | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.FiniteTorDimensionOver | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.FlatConstructibleTensor | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.IntrinsicRealizationTensorComplex | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.IntrinsicResolutionTensorComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.InverseImageExactKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatSingleTensorRepresentative | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KFlatTensorModelNaturalComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalKFlatTensorRoof | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalTensorFiniteFreeZeroModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishing | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTransport | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.PerfectRelativeTensorLocallyBounded | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleCanonicalDerivedPullbackNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleOperations | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelBaseChange | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionNaturality | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionAffineModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartCoordinates | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonFormula | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionKFlatBundledRing | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RelativeTensorStalkGlobalHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RelativeTensorStalkLocalModelHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.RingedSpacePastedUnitKFlatHom | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfExtPushforwardHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionLocal | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfTorOrdinaryResolutionSections | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfTorProjectionHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfTorProjectionHomologyTermwise | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SelfTorPushforwardHomology | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorModel | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectLocalHomComputations | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.SupportQuotientFlat | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates | unclaimed | Unchanged; defeq. |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.LocalizedModuleExactForSystems | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedCechKoszulDualKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedSiteCompleteElementMultiplication | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedToposDerivedAdjunctionOfUniverses | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedToposKFlatPullback | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic | unclaimed | Unchanged; defeq. |
| Sheaf.CategoryTheory.ToposScalarInverseExchangeMate | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.AdicPerfectModelCompleteReduction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.AdicResidueLiftComparisons | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CoefficientEvaluationModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompleteCoefficientDatum | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedAdicCoefficientDatum | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedAdicKoszulKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedConstantSheafReduction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedKoszulQuotientRoosAugmentation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletionMateComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CompletionUnitFiniteProjection | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ConstantCompletionEquivalence | D2 | Unchanged; defeq. |
| Sheaf.Paper.ConstantTwoTermResolution | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DerivedPullbackRepresentativeComputation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DerivedReductionResolutionIndependence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DerivedTowerEvaluationNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.DiagonalTowerSystem | E1 | Unchanged; defeq. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.EtaleKFlatCriteria | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.EvenLineHomShift | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ExactPullbackDerivedAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteCoefficientFlatModel | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteFieldDerivedTensorComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteLineTensorConditions | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.GlobalTensorPullbackKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralHomReductionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralHomReductionModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralModelsOperations | V1 | Unchanged; defeq. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralReductionResidueHomology | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.KFlatMapFactorization | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.KoszulReconstructionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.KoszulReconstructionModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.LocallyConstantTensor | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | K4 | Unchanged; defeq. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.NilpotentReductionStep | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | G6 | Unchanged; defeq. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PerfectQuotientExchangeNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PointDerivedHomModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PointInverseEvaluationKFlat | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PointReductionUnits | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProEtaleCanonicalTensorPullback | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaInverseNaturality | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProjectionMateExact | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PullbackCoefficientIterateCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.Pur9Invertible | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.PurityFiniteKummerDefinitions | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ReductionPullFiniteEvaluation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RestrictedScalarTensorCohomologyComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RestrictionDerivedProducts | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingComplexCechBaseChange | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingComplexFunctorial | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedExchangeTensorCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedLocalizationModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedProjectionRestrictionData | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedSliceDerivedAdjunction | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedSquareTensorCompatibility | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedTensorSquarePresentation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.RingedTopoiDerivedPullback | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SectionDerivedRealization | J8 | Unchanged; defeq. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SemilinearDerivedCalculus | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SemilinearSystemModels | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SfIntegralReductionTower | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SheafSliceDerivedComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ShiftedTensorMorphismCalculus | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SiteTensorLocalModelComparison | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StratumAmbientHom | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StratumScalarExtension | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StrictQuotientScalarBalancing | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StrictQuotientScalarBalancingData | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.StrictScalarCompletionUnit | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.SupportedTorReductionPropagation | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ringedProjectionFormula_totalization_left | unclaimed | Unchanged; defeq. |
| Sheaf.Paper.ringedProjectionFormula_totalization_right | unclaimed | Unchanged; defeq. |
| Sheaf.ProperBaseChange.SingletonSiteModuleComparison | unclaimed | Unchanged; defeq. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Unchanged; defeq. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.EtaleNativeTensorPullback | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.OpenOperationModels | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.RingedDerivedAdjointLift | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.RingedDerivedTwoIsoComparison | unclaimed | Unchanged; defeq. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | unclaimed | Unchanged; defeq. |
| Sheaf.TraceFormula.TwoTermPerfectTorWindow | unclaimed | Unchanged; defeq. |

## Status

landed 20261023T230420-L-3424609 2026-10-23 (merge of deliver/B4/Sheaf.Algebra.Homology.KFlat)
