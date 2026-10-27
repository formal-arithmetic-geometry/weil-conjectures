# AlgebraicGeometry.Scheme.rationalRealizationLocalizedLinear

## Reason

The coefficient-transport theorem needs the exact localized scalar action used by the
item's public comparison predicate. Move that existing construction into the theorem's
new module to avoid an import cycle. The original module publicly reexports it.
No mathematical definition, statement, scalar instance, attribute or body is changed.

## Old

In lean/Sheaf/Paper/ConstructibleRationalHomComparison.lean:

```lean
@[instance_reducible]
def rationalRealizationLocalizedLinear (R : RationalModuleRealization l E X) :
    Linear (Localization.Away (pbcUniformizer l E))
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  letI := R.moduleLinear
  letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    inferInstance
  { homModule := fun M N ↦
      Module.compHom (M ⟶ N) (pbcRationalCoefficientEquiv l E).toRingHom
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (pbcRationalCoefficientEquiv l E a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (pbcRationalCoefficientEquiv l E a) g }
```

## New

The identical declaration above is in lean/Sheaf/Paper/RationalRealizationHomTransport.lean.
The old module publicly imports that module. Its prior rational realization dependency
is reexported by the new module. No existing consumer requires editing; target meanings
and all existing elaborated statements remain identical.

## Users

The downstream scan lists every transitive consumer below; the only textual uses of the
relocated full name were in the item itself. The original direct consumer is
Sheaf.Paper.ContinuousRationalDerivedRealization, which uses the unchanged comparison
predicate and theorem. No consumer signature or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleRationalHomComparison | C7 | Publicly imports the new home of the unchanged scalar structure; all existing public types and bodies preserved. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | A3 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | F2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | X2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | D4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | C3 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | G4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | N3 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | F3 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | S7 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | F7 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | J2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | Q4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | A7 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | B2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | T1 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.DlLocalHeartCoverDefects | H1 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | W9 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | U9 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | V2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | B4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | U9 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | V4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | K1 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | J4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | Y2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | A2 | Moved declaration is publicly reexported under its identical full name and body; no adaptation. |

## Status

landed 20261025T122631-L-1792106 2026-10-25 (merge of deliver/C7/Sheaf.Paper.ConstructibleRationalHomComparison)
