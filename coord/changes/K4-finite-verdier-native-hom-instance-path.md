# WeilConjectures.FiniteProEtaleVerdierBiduality

## Reason

The original native `MonoidalClosed.internalHom` expression elaborates the coefficient
braiding by a different instance path from the generic site-comparison theorem.
Conversion of the specialized functor unfolds derived internal Hom, localization and
derived right adjoints; the complete file repeatedly exceeds its 60-second limit.
The generic helpers kernel-check after the established source-library local instance
priorities are applied (`SymmetricCategory.toBraidedCategory` and
`ProEtale.sheafBraidedCategory`). Directly naming the existing `derivedHom` functor
or transporting the dualizing object by equality is insufficient: the final
specialization still unfolds its native closed structure. Package the original
conjunction once as `ProEtale.VerdierBidualityOn`, with the coefficient category
abstract, and specialize that existing formula to finite coefficients.
The new definition is exactly the original conjunction: preservation and ambient
triangle exactness, the specified restricted anti-equivalence, and invertibility
of the same pairing's canonical biduality map. No hypothesis, object, map, chosen
compactification, finite-Tor predicate or conclusion changes. No source-library
body, signature, attribute or import is changed. All original public imports stay.
A standalone Lean equality check verifies by `rfl` that the direct ModuleCat braiding
and its symmetric-structure projection are equal (clean compile in 4.5 seconds);
the local instance priorities therefore select the same coefficient braiding.

## Old

```lean
noncomputable def FiniteProEtaleVerdierBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  IsExactAntiEquivalenceOn (finiteTorConstructibleProEtaleModule l E n hn Y)
    (MonoidalClosed.internalHom.flip.obj
      ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
        (NagataCompactification aY)).obj (𝟙_ _))) ∧
  ProEtale.HasInvertibleBidualityOn
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y
    ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
      (NagataCompactification aY)).obj (𝟙_ _))
    (finiteTorConstructibleProEtaleModule l E n hn Y)
```

## New

```lean
namespace AlgebraicGeometry.ProEtale

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

noncomputable def VerdierBidualityOn
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))) : Prop :=
  IsExactAntiEquivalenceOn P (MonoidalClosed.internalHom.flip.obj W) ∧
    HasInvertibleBidualityOn A X W P

end AlgebraicGeometry.ProEtale

noncomputable def FiniteProEtaleVerdierBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  ProEtale.VerdierBidualityOn
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y
    ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
      (NagataCompactification aY)).obj (𝟙_ _))
    (finiteTorConstructibleProEtaleModule l E n hn Y)
```

## Users

Read every textual user returned by `tools/downstream.py --uses`:
`FiniteStageVerdierBiduality` applies the comparison using the identical named functor;
`FiniteTorStability` only states the finite-stage conclusion, with an unproved theorem
body; `VerdierCoefficientRealization` includes that same predicate in its coefficient
package. None unfolds its internal Hom, and no adaptation is needed. The unchanged
`VerdierCoefficientRealization` compiled cleanly against the repaired module in
3.5 seconds. The finite-Tor consumer exceeds the fixed limit in the combined
check; its baseline compiled in 41.6 seconds. Diagnostic compilation against the
repair checks all finite-stage declarations, including both occurrences of this
predicate. Its expensive steps lie in unrelated integral comparison/reduction and
rational conclusions (original lines 616, 738 and 1013); no source adaptation is
made. The full consumer timeout is disclosed as a validation limit. All other listed
modules only transitively import the item and have no occurrence of this predicate.
The table records all transitive downstream modules as required, not just textual users.
All statements retain their meaning. The target statement review is reopened by this
(definitionally equal) change of a definition in the target closure; no target text changes.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficients` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficientsData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicRamifiedScalarCochainNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicRamifiedScalarRealizationData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicRealizationIsomorphismNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | A9 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | F7 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ChartDiagonalAssemblyData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CoefFiniteSiteHomTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CommonStagePointReturn` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportCompletedProjectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | Y5 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompleteProjectionMateDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompletedHomScalarTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CompositionTensorMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | D6 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantDirectImageTowerRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionPullbackReturnResidue` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnLocalOperators` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositor` | D8 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalDncAssemblyGlobal` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalDncChartNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalExchangeCube` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationRefinement` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DualBaseChange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.DualizingSigmaCocycleLocality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.EtaleLisseHomReduction` | E8 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ExchangeFunctoriality` | F6 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FdPullbackWeilReturnSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FieldCohomologyPerfectDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | M7 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | K1 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportCoefficientSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportEvaluationRefinement` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | K3 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | G6 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteHomDomainCalculus` | G7 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteHorizontalShriekMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FinitePointReconstructedEvaluationSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeTransposes` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteRationalHeartComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteSheafH0Augmentation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | K4 | Same canonical internal Hom through its existing name; proof completed. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteTargetChangeCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Statement-only use; same predicate meaning; no adaptation. |
| `Sheaf.Paper.FiniteTripleProductNormalForms` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FixProjectionCompactificationComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ForwardProductCoordinateTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeneralChartComparisons` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GermReparametrizationDerivedDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IdentificationCoefficientTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IntegralSectionsPerfectReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IntegralSemilinearGermSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IsomorphismFiniteExchangeCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCompactSupportExchangeData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeProperTensorComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NormalModelSectionOrientation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeProjection` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PerfectDualPairAndTateStability` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PfReductionProperOpenIdentities` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointEquivariantDiagramLift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointPullbackConeLocalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointQuotientTowerHomotopy` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointRestrictionSystemChainMap` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointRestrictionWholeRoosSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointSystemNormalizedComparisonData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointTraceReconstruction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointTransportResolutionCancellation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProductExchangeCounitCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionReductionPresentation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperIntegralTowerComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ProperWeilIterateGermFormula` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | K9 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | M7 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurStrictIntegralExchangeNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurityCompositionCompatibleDncCharts` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.PurityWitnessedMateNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalOrdinaryCohomologyTensor` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalReturnBlockPower` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | V9 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ResidueControlledFiniteHoms` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.RetaggingCoordinateOrientations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SectionDncIntegrationSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexing` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexingData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SemilinearGermIterationDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfBcCompletedMateDomain` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfFieldMateDomain` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfPackageBaseChangeDomainRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationCommonStage` | T1 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SixFunctorMixedSupportCupProduct` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.StrictReductionCompactSupportNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemCompositorRefinementSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemEnrichedProjectionAdjunction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemInternalHomRepresentability` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorExchangeCtfDomains` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCartier` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionProjective` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionSign` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.VectorBundleFrameOrientationRestriction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Statement-only use; same predicate meaning; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilInternalHomWeil` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | X3 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | Y3 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | A5 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProductCompactificationIdentity` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProductSystemUniformRealizationDomain` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | H7 | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.TensorAdjunctionReductionSquares` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.ThreeCellCompositor` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionNormalForm` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.VerdierExchangeData` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleProductTranspose` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.TraceFormula.CompactDirectPowerTransportNormalization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.TraceFormula.FrobeniusCompactPowerExchange` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.TraceFormula.LocalNormalizationStrictRealization` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.TraceFormula.PointConeLiftsChainNaturality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetful` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Transitive import only; no reference to the changed definition; no adaptation. |

## Status

landed 20261025T033921-L-166703 2026-10-25 (merge of deliver/K4/Sheaf.Paper.FiniteStageVerdierBiduality)
