# qcqsStrictLocalRestriction_naturality: retire the duplicate module

## Reason

Retirement assignment in coord/retire-items.tsv and the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The duplicate has zero holes and its
official twin already proves naturality. Their target schemes use different
presentations of the same strict localization, so replacing only the import
would not preserve the small-model consumer.

## Old

The withdrawn module declared the following small-model signature:

```lean
theorem qcqsStrictLocalRestriction_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))
    (hr : ∀ j, r j =
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.smallStrictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictHenselizationStructuralMap s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    ∀ {j k : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)} (a : j ⟶ k),
      F.obj.map ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a).op ≫
        r j = r k
```

QcqsStrictLocalModuleComparison privately imported that module and applied the
theorem when constructing its restriction cocone.

## New

The DAG attachment refers to the existing official theorem:

```lean
theorem qcqsStrictLocalRestriction_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (hr : ∀ j, r j =
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    ∀ {j k : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)} (a : j ⟶ k),
      F.obj.map ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a).op ≫
        r j = r k
```

The duplicate module is withdrawn. Its sole direct consumer imports the official
StrictHenselizationBaseChangeCone directly. The consumer's small-model cocone
naturality is proved inside exists_qcqsStrictLocalModuleComparison: equality of
both pullback projections identifies transported legs with the existing cone;
cone naturality gives refinement compatibility; graph pullback extensionality,
adjunction-unit naturality and contravariant functoriality give the equation.
No public helper duplicates the retired theorem. All four consumer signatures,
all three definition bodies, attributes, and public imports are unchanged.
No adopted source file or target statement changes. The canonical and small
presentations remain related by smallStrictLocalization_toBase and the two
proved projection formulas in SmallStrictLocalSectionMaps.

The naturality node now describes the official proof; the parent comparison
node records the direct small-model calculation instead of citing the retired
small-model theorem. The unit's statement and route are unchanged.

## Users

The source search found one direct importer and one call, both in
QcqsStrictLocalModuleComparison (unclaimed). The six direct importers of that
consumer are compiled unchanged against the adaptation. The full transitive
importer inventory from tools/downstream.py follows; unedited users are insulated
by the identical comparison interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality | N4 | Withdrawn; official theorem retained and attached to its DAG node. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CartierKummerData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.KunnethSupported | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | unclaimed | Unclaimed; imports official twin, proves small-model naturality locally; all signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportLongExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.A1LisseSectionEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicSectionCanonicalModels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AdicSectionClosedSupport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AffineCurveHcZero | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AffineLineInvariance | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AmbTateRootProjectionReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AmbientIndDerivedSums | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ArithmeticRoots | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryDualizingComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryHomVanishing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryQFoundation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryQMaps | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.BoundaryQTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CanonicalRingedRefinementShape | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CartesianCoefficientTwists | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CartesianCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ClopenStrictSystemComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefTowerCoaugmentation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientChangeDualizing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientHeart | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientHeartFiltration | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientHeartGeneration | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CohomologicalSmoothComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonAdicOpenSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonAdicSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageCompactSupportExactness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageFourierTransform | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageWeilFourierTransform | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CommonStageWeilShriek | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactProductProperSupportLaws | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactProductRealizationLaws | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactProductTwistLaws | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportCoefficientAction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportFiniteAction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportLerayFiltration | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportPerfectness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportReductionTower | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompactSupportUniformTorBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompleteCompactSupportProetale | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompletedTensorHomTranspose | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CompositeIntegrationCounit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CondensedBoundedHomContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConnectedConstantH0 | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleExtContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleHomComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ConstructibleProjectionMates | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoordinateCounitArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoordinateGermConcentrationData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CoprojectionCompositionMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CtfHomCoefficientComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CtfHomConditionB | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CtfHomLocalizationDevissage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DeltaProperPushforward | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DeltaRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DerivedGeometricStalk | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DerivedOpenSquareRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DetIndHeartIISums | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerLimit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerSystem | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerTraceLimit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerTraceModels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DiagonalTowerTracePresentations | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DirectImageChangeRingTranspose | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DirectImagesConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DlConstantFieldCharts | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DlConstructibleFibresExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DualStalkFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleCompactScalarCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleRhoMonoidalMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.EtaleSumCoefficientComputation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExceptionalFiniteRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExceptionalProEtaleRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExceptionalSiteRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExtensionByZeroPunctual | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FieldShriekLowerBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FieldTwistInverse | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FieldWeilShriekShiftData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicImageNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicProperSectionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteBoundaryWeights | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteClosedShriek | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCoefficientHomChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCoefficientInputModels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCompactSiteCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteCompactificationWeilExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteConstructibleHom | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteEtaleDescent | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteExceptionalInternalHom | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteIndHeartAdjunction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteProductCompactification | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteProjectionActionLaws | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteRingSectionDeformation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteStageVerdierBiduality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteTateSiteDescent | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteWeilIndPushExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteWindow | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteWindowBounded | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FiniteWindowUnbounded | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FormalClosedSupport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FormalClosedSupportII | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FormalClosedSupportIILimits | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FourierTraceFormula | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusGeometricExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.FrobeniusSquareExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.GlobalGeometricFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.HomFiniteProjective | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndConstructibleExtensions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndHeartFullFaithfulness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndHeartIIVanishing | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IndHeartKernelsCokernels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralAmbientTowerComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstantModelHeart | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleCompactness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleExt | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleHeart | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleInternalHom | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralExceptionalInverseImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralHeartDualizable | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralHeartLocalModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralHeartRealizationExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralHeartResidueDual | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralIndConstructibleStability | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralIndHeartRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralIndLowerTail | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralLineDerivedComparisons | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralLinePowerComparisons | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralLineReductionDefinitions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralLineReductionRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralLineRestrictions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralModels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralModelsOperations | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralProperBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralQuotientCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralQuotientProjectionMap | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralStratumExtBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralStratumHomFormula | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTensorProduct | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTensorPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTwistBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTwistDerivedScalar | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralTwistScalarCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntegralWindowCoproductComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.InternalHomDualConstructibleModels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.InternalHomPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IteratedWeilCocycle | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.IteratedWeilMap | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.KummerAdditivity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LatticeSubquotientFiltration | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LisseCohomologyDerivedDual | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LisseDenseOpenRecovery | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LisseExtensionInertia | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocalizedDirectImageComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.MiddleExtensionHcZero | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.MixedReductionUnit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.NearbyProperHyperdescent | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.NormalizedCoefficientFamilies | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.OrdinaryCompactCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PbcCoefficientTwists | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PfRefinementCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PoincarePointFiniteness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PointCompletedEvaluation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PointIdentityAdmissibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProEtaleTateTwists | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperBaseChangeRational | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperCompactCoincidence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperHeartBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperHeartBoundLattice | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperHeartBoundReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperOpenCoefficientMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperOpenTowerComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityConventions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityCoprojection | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityExteriorProductFrame | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityFiniteKummerLevel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityFrameClass | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityFrameKummer | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityFramePrincipalBoundary | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityGysinStructure | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityRankOneLocalCalculation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PuritySourceTransports | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.PurityTwistCancellation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QbarTwistCommonStage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QcqsCompactSupportRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QlbarDirectImageComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalClosedSupportConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalDirectImageRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalLocalizedHom | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RationalStalkExact | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RealWeights | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RefinementExchangeCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RelativeSupportCoordinateModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ResidueControlledFiniteHoms | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementClopen | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementConstruction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementCore | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RingedRefinementFinite | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ScalarModelImmersionExtension | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SectionCentredChartData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SectionLocalComparisonData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SectionLocalDualizingComparisons | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SemilinearFieldOperationLifts | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfCommonStageDirectImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfProEtaleProjectionFormula | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SignedTwistReductionComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SitePerfectCoefficientDual | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SitePerfectDualizableHom | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SixFunctorDatum | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SixFunctorDualNotation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SixFunctorOperationDatum | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SixFunctorOperationDatumStages | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityQbar | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityTowerBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityTowerClasses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.StratifiedConstantModelProductBound | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.StratifiedLatticeRank | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedClassGeometry | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedClassSiteComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedCupFunctoriality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedExteriorClassArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedExteriorClasses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedExteriorShift | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedHomCocycleNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedHomPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedTwistMultiplication | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SupportedTwistPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SystemClopenTensorCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SystemOperationExchangeRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.SystemTensorMateArrows | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TameRootTowerExtension | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TateTwistLisseLine | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TateTwistLocallyFree | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassChern | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassCoefficients | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassDiagonal | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassFinite | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassFiniteDiagonal | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassProjective | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassSystems | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TowerClassTwisting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceBaseChangeFirst | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceCompactificationCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFixedScheme | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFormulaAdicSystem | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TraceGraphCorrespondence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TrfWitnessedOpenPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TwConventions | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TwFrobeniusAction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.TwistPreservesFiniteness | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.UnboundedProperOpenInterchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.UniformConstructibleExt | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.UniformConstructibleExtRational | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorBundlePurity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorPurityBaseChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorPurityDirectSum | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorPurityFiniteReduction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorPurityNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.VectorPurityScalarSingle | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilCompactSupportCohomology | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilFourierPlancherel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilInternalHomWeil | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilMixedUpperBounds | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilOpenImageDelta | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilShriekShiftCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WeilTateTwistFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WfTateTwist | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WfTateTwistCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ZlFrameworkOpenExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Paper.ZlShriekComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.BoundaryDualityInput | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.CompactCoefficientComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.CompositionProjectionMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.FieldTensor | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralOperationShiftData | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralSystemOperations | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.InternalHomPullback | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenFactorCoherence | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenFactorPullModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenFactorTensorModel | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Targets.PoincareTateBoundedConstructible | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.Targets.VectorBundlePurity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |
| Sheaf.ZetaWeil.WeightPurityRoots | not edited | Transitive consumer; unchanged comparison API and mathematical meaning. |

## Status

landed 20261021T203716-L-3857412 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality)
