# WeilConjectures.sfRationalDirectImageCoefficientCompatibility

## Reason

The item concerns arbitrary finite-type schemes over k, while the coefficient-only
interface was restricted to specified geometric fibers of finite-field models.
The normalized coefficient pullback comparisons and the finite-free coefficient
right-mate argument do not use a finite-field model. Generalize this lower theorem
rather than add a duplicate statement or choose arbitrary data. No pointwise right
adjoint existence is asserted on arbitrary schemes: every right adjoint and its
adjunction are inputs to the mate clause. The original finite-field cases are retained.

The source is Bhatt--Scholze 6.7.2, 6.8.14(2), Remark 6.8.15. Its coefficient
argument uses finite freeness, finite sums, normalized tensor associators and
rightAdjointUniq; all are independent of a finite-field presentation. Identity
coefficient inclusions use the tensor unit; empty schemes, zero objects and
nonseparated schemes cause no extra hypothesis. The parent target signatures and
the meanings of all their definitions are unchanged. This record concerns a
stronger lower theorem with its original proof hole, not a proof of that theorem.

## Old

```lean
theorem sfRationalDirectImageCoefficientCompatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f : X₀ ⟶ Y₀) :
    letI := sfWeilPrimeInvertible D l hl X₀
    letI := sfWeilPrimeInvertible D l hl Y₀
    ∃! L : (stageSystem l Ω (D.geometricFiber Y₀).left).Morphism
        (stageSystem l Ω (D.geometricFiber X₀).left),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) (zlFiberMap D f)) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          (D.geometricFiber Y₀).left),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω (zlFiberMap D f) ⟨E, K⟩ F h)) ∧
      ∀ (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber X₀).left ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber Y₀).left)
        (a : ∀ E, L.Φ E ⊣ R E),
        ∀ {E F : Index l Ω} (h : E ≤ F),
          IsIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans)
```

## New

```lean
theorem sfRationalDirectImageCoefficientCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! L : (stageSystem l Ω Y).Morphism
        (stageSystem l Ω X),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          Y),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h)) ∧
      ∀ (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            X ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            Y)
        (a : ∀ E, L.Φ E ⊣ R E),
        ∀ {E F : Index l Ω} (h : E ≤ F),
          IsIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans)
```

## Users

The source search `tools/downstream.py Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility --uses sfRationalDirectImageCoefficientCompatibility`
found one existing external occurrence, in SfRationalDirectImageAdjunction.
The following table includes every transitive downstream module reported by the
script, plus the changed module. No adopted source-tree module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficients | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficientsData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicRamifiedScalarCochainNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicRamifiedScalarRealizationData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CommonStageWeilShriek | C6 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CompositionTensorMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DualBaseChange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExchangeFunctoriality | F6 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FieldWeilShriekShiftData | F7 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | M7 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | F9 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | G6 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteTorStability | E5 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | K4 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Item: use the generalized theorem to prove its adjoint-existence hole; definitions unchanged. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GeometricOperations | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointQuotientTowerHomotopy | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointRestrictionSystemChainMap | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurIntegralRepresentingPair | K9 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurIntegralSupportComparison | M7 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ReducedFrontierMixedGluing | V9 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | T1 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Only direct Lean caller: specialize to zlFiberMap D f. All declaration signatures stay verbatim. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Generalize the coefficient-only theorem; its existing named proof hole remains. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwConventions | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | U3 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.TensorHomSignedTransposes | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SixFunctors.WeilChosenDualityHom | D2 | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer only; no occurrence of the changed declaration, no edit or semantic change. |

## Status

landed 20261024T232204-L-2311194 2026-10-24 (merge of deliver/C2/Sheaf.Paper.GeometricCommonStageDirectImage)
