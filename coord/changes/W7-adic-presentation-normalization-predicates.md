# AlgebraicGeometry.Scheme.HasAdicPresentationConstantNormalization

Also: `AlgebraicGeometry.Scheme.HasAdicPresentationEvaluationNormalization`.
Group W7, item `Sheaf.Paper.AdicPullbackPresentationTransport`.

## Reason

The original holed module took about 47 seconds. The two concrete normalization
predicates repeatedly expand the completed scalar-extension pullback while checking
their equations; completed proofs exceeded 60 seconds. A generic representative
normalization predicate avoids repeating this concrete categorical type checking.
The retained predicates unfold to exactly their former equations. The evaluation
complex `P.asFunctor.obj (op k)` is definitionally the former termwise evaluation.
No existing signature, public import, hypothesis, conclusion, or target meaning changes.
The coefficient maps, finite quotients, completion units and localized adjunctions stay
as before. No source-library module or module held by another group is edited.

## Old

```lean
def HasAdicPresentationConstantNormalization
    (b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
    (completedDerivedConstant d X).map
        (Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε P) ≫
      ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P)) =
    b.hom.app (DerivedCategory.Q.obj P) ≫
      T.map (((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P) ≫
      Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ
        (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def HasAdicPresentationEvaluationNormalization (n : ℕ)
    (v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L) : Prop :=
  ∀ P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ,
    (∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op k)).mapHomologicalComplex (.up ℤ)).obj P)) →
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
        (Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (adicPresentationEvaluationComplex_eq g d n P)) =
    v.hom.app (DerivedCategory.Q.obj P) ≫
      L.map (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app P) ≫
      Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε
        ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj P)
```

## New

A generic helper, in the same Sheaf module:

```lean
def CategoryTheory.Functor.HasRepresentativeNormalization
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (L : C ⥤ E) (T : D ⥤ F) (H : E ⥤ F) (G : C ⥤ D)
    {I : Type*} (good : I → Prop)
    (q : I → C) (k : I → D) (p : I → E) (z : I → F)
    (a : ∀ i, L.obj (q i) ⟶ p i) (c : ∀ i, T.obj (k i) ⟶ z i)
    (f : ∀ i, G.obj (q i) ⟶ k i) (l : ∀ i, H.obj (p i) ⟶ z i)
    (b : L ⋙ H ≅ G ⋙ T) : Prop :=
  ∀ i, good i → H.map (a i) ≫ l i = b.hom.app (q i) ≫ T.map (f i) ≫ c i
```

```lean
def HasAdicPresentationConstantNormalization
    (b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T) : Prop :=
  Functor.HasRepresentativeNormalization L T
    (completedDerivedConstant d X) (completedDerivedConstant d Y)
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P)
    (fun P ↦ DerivedCategory.Q.obj P)
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)))
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε P)
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ ((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P)
    (fun P ↦ ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P))) b
```

```lean
def HasAdicPresentationEvaluationNormalization (n : ℕ)
    (v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L) : Prop :=
  Functor.HasRepresentativeNormalization T L
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n)
    (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n)
    (fun P ↦ ∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion Y d) (P.asFunctor.obj (op k)))
    (fun P ↦ DerivedCategory.Q.obj P)
    (fun P ↦ DerivedCategory.Q.obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ DerivedCategory.Q.obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj P)))
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ P)
    (fun P ↦ Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P))
    (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules Y (pbcAdicCompletion Y d))).obj (op n)).mapDerivedCategoryFactors.hom.app P)
    (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules X (pbcAdicCompletion X d))).obj (op n)).mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (adicPresentationEvaluationComplex_eq g d n P))) v
```

Unfolding the generic helper gives the old predicates, so each remains the same
proposition on every representative, including zero complexes and empty sites.
The constant and evaluation proofs now manipulate this equation generically. All
helpers are proved and there are zero new proof holes. Existing statement signatures
and public imports were compared with live source: all 31 existing declarations match.
Full compile and delivery verification results are recorded in the item report.

## Users

The downstream scan finds 307 transitive importers. Searching each changed
predicate finds only this item module itself (three constant-predicate and four
evaluation-predicate occurrences in the original). Each listed external module
receives identical signatures and definitionally equal predicate bodies. No external
source adaptation is needed. Claims below are the current records at the check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPullbackPresentationTransport | W7 | Both definition bodies refactored; proofs updated; meaning preserved |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | R9 | Same interface and predicate meaning; no adaptation |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CanonicalOpenRestrictionModel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompleteCompactSupportProetale | B7 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompleteProetale | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedCoefficientPullbackLinearity | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedOpenExchangeTransport | G5 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | Y9 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | B3 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.OpenRestrictionCompleteness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RationalRealizationPullbackComparison | J8 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RealWeights | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | P8 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfExchanges | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassChern | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TwConventions | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WfTateTwist | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenQuotientKoszulCompleteness | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | T5 | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same interface and predicate meaning; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same interface and predicate meaning; no adaptation |

## Status

landed 20261021T214915-L-1888546 2026-10-21 (merge of deliver/W7/Sheaf.Paper.AdicPullbackPresentationTransport)
