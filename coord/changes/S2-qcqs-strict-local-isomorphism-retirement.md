# AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula

## Reason

The assigned item is a zero-hole retirement in coord/retire-items.tsv. The human's
retirement hand-off in coord/changes/retire-sheaf-twins-20261020.md requires removing
the Sheaf duplicate. The adopted theorem uses strictLocalizationToBase, while the
copy and its sole direct consumer use strictHenselizationStructuralMap. These are
canonically isomorphic presentations, not definitionally equal schemes.

Remove the duplicate. In the sole direct consumer, prove invertibility within the
existing comparison construction, from the official set comparison and the general
module section transport theorem. The canonical small/full ring-colimit isomorphism
and pullback symmetry identify the graph maps; the given cocone equations identify
the transported map with the bijective official set comparison. This preserves every
consumer signature, definition and public import, without a renamed duplicate or a
new hole. The assigned node points at the adopted source theorem, whose statement
and proof remain unchanged. The consumer's node records its direct argument instead.

## Old

The removed duplicate's signature was:

```lean
theorem isIso_qcqsStrictLocalRestriction_of_formula
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))
    (ha : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
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
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) : IsIso a
```

The direct consumer imported the item privately and used:

```lean
  have : IsIso a := isIso_qcqsStrictLocalRestriction_of_formula Λ f s F a ha
```

## New

The Sheaf declaration is withdrawn, not renamed or weakened. Its node attaches to:

```lean
theorem isIso_qcqsStrictLocalRestriction_of_formula
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (ha : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
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
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) : IsIso a
```

The direct consumer privately imports Sheaf.AlgebraicGeometry.ModuleSectionsIsoTransport
and proves IsIso a locally inside exists_qcqsStrictLocalModuleComparison. Its public
signature and all three public definition bodies remain verbatim. The options for
elaborating the transport argument are scoped to that theorem. The former import was
private, so no indirect consumer could use its declaration through that import.
The unchanged target includes the empty scheme and the zero coefficient ring; the
proof adds no nonemptiness, properness or torsion assumption.

## Users

The project downstream.py --uses scan found just the direct consumer and the withdrawn
module mentioning the removed declaration. The following table lists every downstream
module from downstream.py --names; indirect consumers retain the direct consumer's
identical public interface. The direct consumer is unclaimed in the current claims
inventory and is the only adapted module. No source-library module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CartierKummerData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.KunnethSupported | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | unclaimed | Adapted proof and private import; all public signatures and definition bodies unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportLongExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.A1LisseSectionEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPurityFiniteTensor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPurityObjects | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPurityRootComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPuritySourceReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicPurityTwistReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicSectionCanonicalModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicSectionClosedSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineCurveHcZero | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineLineInvariance | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineLinePurityComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineLinePuritySource | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AffineTranslationTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AmbTateRootProjectionReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AmbientIndDerivedSums | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ArithmeticRoots | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryDualizingComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryHomVanishing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryQFoundation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryQMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BoundaryQTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.BrownHypothesesGeneration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CanonicalRingedRefinementShape | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CartesianCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CartesianCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CartierClassAgreement | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ChernFlagFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ClopenStrictSystemComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ClosedSupportConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefTowerCoaugmentation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientChangeDualizing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientHeart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientHeartFiltration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientHeartGeneration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CohomologicalSmoothComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonAdicOpenSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonAdicSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageCompactSupportExactness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageFourierTransform | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageWeilFourierTransform | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CommonStageWeilShriek | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactProductProperSupportLaws | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactProductRealizationLaws | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactProductTwistLaws | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportCoefficientAction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportFiniteAction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportLerayFiltration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportNormalizedRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportPerfectness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportReductionTower | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactSupportUniformTorBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactificationCompletedRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompactifiedTowerComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompleteCompactSupportProetale | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompletedTensorHomTranspose | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CompositeIntegrationCounit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CondensedBoundedHomContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConnectedConstantH0 | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstantExtensionMixedDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstantGeometricStalkUnit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleCompactness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleExtContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleHomComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ConstructibleProjectionMates | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoordinateCounitArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoordinateGermConcentrationData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CoprojectionCompositionMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CtfHomCoefficientComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CtfHomConditionB | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CtfHomLocalizationDevissage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DeltaRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DerivedGeometricStalk | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DerivedOpenSquareRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DetIndHeartIISums | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientCategory | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientQuotients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientReference | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientScalars | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerLimit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerSystem | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerTraceLimit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerTraceModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DiagonalTowerTracePresentations | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DirectImageChangeRingTranspose | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DirectImagesConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DlConstantFieldCharts | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DlConstructibleFibresExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DualStalkFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DualizingObjectPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.DualizingUnitComposite | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleCompactScalarCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleRhoMonoidalMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.EtaleSumCoefficientComputation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExceptionalFiniteRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExceptionalProEtaleRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExceptionalSiteRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExtensionByZeroPunctual | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FieldShriekLowerBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FieldTwistInverse | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FieldWeilShriekShiftData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicImageNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicProperSectionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteBoundaryWeights | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteClosedShriek | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCoefficientHomChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCoefficientInputModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCompactSiteCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteCompactificationWeilExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteConstructibleHom | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteEtaleDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteExceptionalInternalHom | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteIndHeartAdjunction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteProductCompactification | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteProjectionActionLaws | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteProperLocalizing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteReductionChartCalculus | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteReductionComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteReductionOfPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteReductionRootCharts | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteRingSectionDeformation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSiteCoordinates | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSiteTensorProjection | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteStageVerdierBiduality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteTateSiteDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteWeilIndPushExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteWindow | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteWindowBounded | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FiniteWindowUnbounded | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FlagLocalComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FlagPullbackInjective | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FormalClosedSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FormalClosedSupportII | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FormalClosedSupportIILimits | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FourierTraceFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusGeometricExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.FrobeniusSquareExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.GlobalGeometricFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.HomFiniteProjective | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndConstructibleExtensions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndHeartFullFaithfulness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndHeartIIVanishing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IndHeartKernelsCokernels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralAmbientTowerComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstantModelHeart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleCompactness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleExt | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleHeart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleInternalHom | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralExceptionalInverseImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralHeartDualizable | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralHeartLocalModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralHeartRealizationExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralHeartResidueDual | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralIndConstructibleStability | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralIndHeartRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralIndLowerTail | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralLineDerivedComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralLinePowerComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralLineReductionDefinitions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralLineReductionRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralLineRestrictions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralModelsOperations | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralProperBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralQuotientCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralQuotientProjectionMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralStratumExtBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralStratumHomFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTensorProduct | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTensorPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistDerivedScalar | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistScalarCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntegralWindowCoproductComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.InternalHomDualConstructibleModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.InternalHomPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IteratedWeilCocycle | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.IteratedWeilMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerAdditivity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerChartGeometryMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerCoefficientModels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerCoherentRoof | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerConstantNerveTerm | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerGeometricColumns | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerGlobalChart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerInvariantScalarMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerLocalSource | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerNerveCoordinates | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerNerveGeometricMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerNerveTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerNormalizedChart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerParameterizedTerm | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerRefinement | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerResolvedDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerScalarInvariantSquare | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerStratumChart | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.KummerStratumGeometry | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LatticeSubquotientFiltration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LineZeroClassEtaleRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LisseCohomologyDerivedDual | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LisseDenseOpenRecovery | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LisseExtensionInertia | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalizedDirectImageComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalizedFlagProduct | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalizedTopChern | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.MiddleExtensionHcZero | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.MixedReductionUnit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.NearbyProperHyperdescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.NormalizedCoefficientFamilies | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OpenImmersionLocalizing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OpenScalarSiteCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrdinaryCompactCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationEtaleFamily | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationFiniteReductionTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationGeometricComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PbcCoefficientTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PfRefinementCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PoincarePointFiniteness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointCompletedEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointIdentityAdmissibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointSectionsCompletionCone | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointSystemRoosTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointSystemTransportDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointTransportConeComparisonDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointTransportStrictQuotient | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PointWeilHeartFlag | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleAffineLineCounit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleFrameIntegration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleOrderedIntegration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleProjectionIntegration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleTateTwists | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleVectorIntegration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProjectiveBundleFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperBaseChangeRational | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperCompactCoincidence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperHeartBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperHeartBoundLattice | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperHeartBoundReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperOpenBoundaryZero | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperOpenCoefficientMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperOpenTowerComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurAdicReconstruction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityAffineLineOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityAffineLineSupportStalk | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityChernClasses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityCompositionCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityConventions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityCoprojection | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityDiagonalSectionPasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityDivisorClass | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityExteriorProductFrame | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFiniteKummerLevel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFrameClass | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFrameIndependence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFrameKummer | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityFramePrincipalBoundary | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityGysinStructure | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityRankOneLocalCalculation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityRankOneLocalData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityRelativeKummer | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PuritySourceTransports | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.PurityTwistCancellation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QbarTwistCommonStage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QcqsCompactSupportRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QlbarDirectImageComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RankOneClassicalSupportComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RankOneKummerGenerator | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RankOneKummerMonomial | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalClosedSupportConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalDirectImageRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalLocalizedHom | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RationalStalkExact | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RealWeights | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ReducedFrontierMixedGluing | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RefinementExchangeCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RegularImmersionCancellation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RegularImmersionClassData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RegularImmersionExteriorClass | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RegularImmersionPurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RelativeSupportBottomDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RelativeSupportCoordinateModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ResidueControlledFiniteHoms | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementClopen | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementConstruction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementCore | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RingedRefinementFinite | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RootBoundaryComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RootBoundaryScalarComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RootTowerInnerSupport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ScalarModelImmersionExtension | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SectionCentredChartData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SectionLocalComparisonData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SectionLocalDualizingComparisons | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SemilinearFieldOperationLifts | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfCommonStageDirectImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfProEtaleProjectionFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SignedTwistReductionComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SitePerfectCoefficientDual | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SitePerfectDualizableHom | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorDatum | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorDualNotation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOperationDatum | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOperationDatumStages | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientationDatum | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientationFamily | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityMap | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityQbar | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityTowerBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityTowerClasses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SmoothTrace | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.StratifiedConstantModelProductBound | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.StratifiedLatticeRank | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedAffineLineHomotopy | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedClassGeometry | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedClassSiteComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedCupFunctoriality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedExteriorClassArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedExteriorClasses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedExteriorShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedHomCocycleNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedHomPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedProjectionSplitting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedProjectiveChern | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedTwistMultiplication | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SupportedTwistPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SystemClopenTensorCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SystemOperationExchangeRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.SystemTensorMateArrows | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TameRootTowerExtension | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TameStratumKummerDescent | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TateTwistLisseLine | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TateTwistLocallyFree | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassChern | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassCoefficients | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassDiagonal | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassFinite | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassFiniteDiagonal | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassProjective | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassSystems | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerClassTwisting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceBaseChangeFirst | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceCompactificationCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFixedScheme | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFormulaAdicSystem | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TraceGraphCorrespondence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TrfDevissageGeneration | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TrfWitnessedOpenPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TwConventions | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TwFrobeniusAction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TwistFrobeniusScalar | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.TwistPreservesFiniteness | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.UnboundedProperOpenInterchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.UniformConstructibleExt | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.UniformConstructibleExtRational | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorBundlePurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorBundleThomClass | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorIntegrationSiteComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorPurityBaseChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorPurityDirectSum | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorPurityFiniteReduction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorPurityNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorPurityScalarSingle | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.VectorTensorSiteEquations | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilCompactSupportCohomology | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilFourierPlancherel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilInternalHomWeil | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilMixedUpperBounds | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilOpenImageDelta | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilShriekShiftCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WeilTateTwistFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WfTateTwist | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WfTateTwistCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ZlFrameworkOpenExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Paper.ZlShriekComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.BoundaryDualityInput | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.CompactCoefficientComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.CompositionProjectionMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.FieldTensor | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralOperationShiftData | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralSystemOperations | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.InternalHomPullback | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenFactorCoherence | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenFactorPullModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenFactorTensorModel | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Targets.PoincareTateBoundedConstructible | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.Targets.VectorBundlePurity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not edited | Not edited; indirect consumer of the unchanged public interface. |
| Sheaf.ZetaWeil.WeightPurityRoots | not edited | Not edited; indirect consumer of the unchanged public interface. |
| WeilConjectures | not edited | Not edited; indirect consumer of the unchanged public interface. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not edited | Not edited; indirect consumer of the unchanged public interface. |

## Status

landed 20261022T002436-L-1930859 2026-10-22 (merge of deliver/S2/Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism)
