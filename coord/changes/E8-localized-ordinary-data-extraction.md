# AlgebraicGeometry.Scheme.LocalizedOrdinary.Edge

## Reason

The three independent proof steps need the existing normalization data without
importing their own parent theorem. Move all auxiliary declarations verbatim into
Sheaf.Paper.LocalizedOrdinaryPullbackData, publicly re-exported by the item module.
The same names, universes, signatures, attributes and bodies are preserved. This is
an extraction, with no change to the meaning of a target or of any definition.
The original node retains the main theorem attachment; the new definition node
records the existing data in their new module.

## Old

In lean/Sheaf/Paper/LocalizedOrdinaryPullbackNormalization.lean:

```lean
structure Edge where
  coefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R l E ϖ X) ⟶ R l E ϖ Y
  coefficient_unit : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (iota l E ϖ X) ≫
    coefficient = completedCoefficientMap g (pbcIntegralDatum l E) ≫ iota l E ϖ Y
  ordinary : pbcActualModulePull g (pbcIntegralDatum l E) ⋙ F₀ l E ϖ Y ≅
    F₀ l E ϖ X ⋙ G₀ l E ϖ g coefficient
  ordinary_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (integralUnitSection l E g M V m)) =
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_tensor : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (b : (B l E Y).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (iota l E ϖ Y)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) e
        (b • integralUnitSection l E g M V m)) =
    (e * (iota l E ϖ Y).hom.app (op ((proEtaleBaseChange g).obj V)) b) •
      unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)
  ordinary_inverse_unit : ∀ (M : pbcModules X (B l E X)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (R l E ϖ Y).obj.obj (op ((proEtaleBaseChange g).obj V))),
    (ordinary.inv.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (e • unitSection l E ϖ g coefficient ((F₀ l E ϖ X).obj M) V
        (pbcTensorSection (iota l E ϖ X) M (op V) 1 m)) =
    pbcTensorSection (iota l E ϖ Y)
      ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
      (op ((proEtaleBaseChange g).obj V)) e
      (integralUnitSection l E g M V m)
  derived : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙ F l E ϖ Y ≅
    F l E ϖ X ⋙ G l E ϖ g coefficient
  derived_model : ∀ P : CochainComplex (pbcModules X (B l E X)) ℤ,
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} _) (ProEt.topology X) (B l E X) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := B l E X) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (G l E ϖ g coefficient).map (pbcComplexCounit (iota l E ϖ X) P) ≫
      counit l E ϖ g coefficient
        (((F₀ l E ϖ X).mapHomologicalComplex (.up ℤ)).obj P) =
    (F l E ϖ Y).map (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
      pbcComplexCounit (iota l E ϖ Y)
        (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
```

The other relocated declarations are B, uniformizer, R, iota, F₀, F,
integralUnitSection, G₀, G, counit, unitSection, scalarSection, Composition,
Identity and Coefficients in namespace AlgebraicGeometry.Scheme.LocalizedOrdinary.
Their complete original bodies are the initial data section of the item module.

## New

The declaration above and every other listed auxiliary declaration are byte-for-byte
identical in lean/Sheaf/Paper/LocalizedOrdinaryPullbackData.lean. The only differences
in that section are its module title and blueprint docstring tags. The item now has:

```lean
public import Sheaf.Paper.LocalizedOrdinaryPullbackData
```

This publicly re-exports every original public import and auxiliary declaration.
Only the main theorem proof is replaced, using a proved coefficient theorem and
three strictly smaller construction/coherence statements.

## Users

The conservative table below includes every transitive importer, including modules
that only contain an unrelated short name such as B or F. There are no external
qualified references to the relocated declarations. This also covers the broad
syntactic consumer advisories; none has a changed signature or definition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LocalizedOrdinaryPullbackNormalization | E8 | Main proof assembled from normalized comparisons and proved coefficients. |
| Comparator.Weil.Solution | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | W4 | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | C7 | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | X2 | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | C8 | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | E5 | Public re-export and definitions identical; no adaptation. Sole direct importer, compiled unchanged. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Public re-export and definitions identical; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public re-export and definitions identical; no adaptation. |
| TargetsCheck | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | C4 | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public re-export and definitions identical; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public re-export and definitions identical; no adaptation. |

There are 297 transitive importers (read-only import graph, agreeing with
tools/downstream.py). The only direct importer was compiled against the packet.
No existing module besides the item is changed, and no source-library declaration is touched.

## Status

landed 20261027T012824-L-2336455 2026-10-27 (merge of deliver/E8/Sheaf.Paper.LocalizedOrdinaryPullbackNormalization)
