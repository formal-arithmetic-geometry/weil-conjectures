# AlgebraicGeometry.Etale.bijective_qcqsStrictLocalRestriction_of_formula

## Reason

The assigned module is a zero-hole retirement item in coord/retire-items.tsv.
The human hand-off in coord/changes/retire-sheaf-twins-20261020.md requires withdrawing
this duplicate in favor of its adopted source twin. The two statements use canonically
isomorphic strict-local models: the Sheaf copy uses strictHenselizationStructuralMap
and the adopted source uses strictLocalizationToBase. A bare import replacement would
change the direct consumer's target and representative formula.

Retain the source theorem unchanged. In the direct consumer, use the official set
comparison instead: base change Spec.map (smallStrictHenselizationColimitIso s).inv,
compose with pullback symmetry, and apply exists_moduleSectionsIsoTransport. Its
formula and the definition of smallStrictHenselizationBaseChangeMap identify the
transported representative maps. The uniqueness and bijectivity of the official set
comparison then prove the original isomorphism statement. No old proof is moved to
a renamed duplicate, no new declaration is introduced, and no hole is added.

## Old

The removed duplicate had the following signature:

```lean
theorem bijective_qcqsStrictLocalRestriction_of_formula
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
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    Function.Bijective (ConcreteCategory.hom a)
```

The direct consumer imported the duplicate privately and applied that theorem to a
and ha, then used ConcreteCategory.isIso_iff_bijective.

## New

The node now attaches to the existing adopted declaration:

```lean
theorem bijective_qcqsStrictLocalRestriction_of_formula
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
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    Function.Bijective (ConcreteCategory.hom a)
```

The direct consumer's signature, universes, visibility, hypotheses and all public imports
are byte-for-byte unchanged. Its proof transports the original map only as a set map;
the equivalence is chosen inside this theorem from a fully proved existence theorem,
and it is never used as data for a definition. The final module isomorphism is about
the original given linear map. The theorem covers empty X and the zero coefficient
ring: the same canonical isomorphisms and composition-of-bijections argument apply,
with no choice of a section and no nonzero assumption.

The bijectivity node's proof dependencies now describe the unchanged adopted proof.
The isomorphism node's proof dependencies describe the new direct set comparison.
The unit sk-thm-iff and its realized route are unchanged. No source-library or target
file, definition, or statement is edited. The only existing declaration removed is
the explicitly assigned Sheaf duplicate.

## Users

The following is the complete transitive list from tools/downstream.py, with its
--uses check finding only the duplicate itself and the direct consumer as textual
users of the removed theorem. The direct consumer is unclaimed in the current
shared claim records. Transitive consumers are listed for interface review and are
not edited, so their holders' work is unaffected.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective | W2 | Withdraw the duplicate; reattach its node to the adopted source theorem. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism | unclaimed | Replace the proof and private import; preserve the complete public signature verbatim. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportLongExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.A1LisseSectionEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPurityObjects | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AffineCurveHcZero | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AffineLineInvariance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AmbTateRootProjectionReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AmbientIndDerivedSums | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ArithmeticRoots | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryDualizingComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryHomVanishing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryQFoundation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryQMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BoundaryQTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementShape | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CartesianCoefficientTwists | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CartesianCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CartierClassAgreement | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ChernFlagFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ClosedSupportConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefTowerCoaugmentation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientHeart | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientHeartFiltration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientHeartGeneration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CohomologicalSmoothComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonAdicOpenSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonAdicSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageCompactSupportExactness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportCoefficientAction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportFiniteAction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportPerfectness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportReductionTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactSupportUniformTorBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactificationCompletedRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactificationLocalizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactificationRefinementIdentity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CompositeIntegrationCounit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CondensedBoundedHomContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstantGeometricStalkUnit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleCompactness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleExtContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleHomComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ConstructibleProjectionMates | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoordinateCounitArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoordinateGermConcentrationData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CoprojectionCompositionMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CtfHomConditionB | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CtfHomLocalizationDevissage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DeltaRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DerivedOpenSquareRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DerivedTruncationCoproducts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DetIndHeartIISums | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerSystem | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerTraceLimit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerTraceModels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DiagonalTowerTracePresentations | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DirectImageChangeRingTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DirectImagesConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DualStalkFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DualizingObjectPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.DualizingUnitComposite | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleCompactScalarCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.EtaleSumCoefficientComputation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalFiniteRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExceptionalSiteRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FieldShriekLowerBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FieldTwistInverse | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteClosedShriek | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientInputModels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCompactSiteCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteConstructibleHom | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteEtaleDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteExceptionalInternalHom | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeCompactComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeCompactScalar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteFreeScalarProjection | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteProductCompactification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteProjectionActionLaws | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteProperLocalizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteStageVerdierBiduality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteTorStability | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteWindow | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteWindowBounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FlagLocalComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FlagPullbackInjective | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FormalClosedSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FormalClosedSupportII | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FormalClosedSupportIILimits | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FourierTraceFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusGeometricExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.HomFiniteProjective | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndConstructibleExtensions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndHeartFullFaithfulness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndHeartIIVanishing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IndHeartKernelsCokernels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralAmbientTowerComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstantModelHeart | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleCompactness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleExt | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleHeart | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleInternalHom | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralHeartDualizable | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralHeartLocalModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralHeartRealizationExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralHeartResidueDual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralIndConstructibleStability | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralIndHeartRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralIndLowerTail | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLineDerivedComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLinePowerComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLineReductionDefinitions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLineReductionRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLineRestrictions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralModels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralModelsOperations | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralProperBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralProperProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralQuotientCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionMap | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralStratumExtBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralStratumHomFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTensorProduct | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTensorPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistScalarCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntegralWindowCoproductComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.InterchangeProperPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.InternalHomDualConstructibleModels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.InternalHomPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IteratedWeilCocycle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.IteratedWeilMap | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.KummerAdditivity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LatticeSubquotientFiltration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LisseCohomologyDerivedDual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LisseExtensionInertia | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizedDirectImageComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizedTopChern | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.MateOpenRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.MixedReductionUnit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NearbyProperHyperdescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NonrationalCompositionSeed | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OpenImmersionLocalizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OpenScalarSiteCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OrdinaryCompactCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PbcCoefficientTwists | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PfRefinementCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointIdentityAdmissibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointSectionsCompletionCone | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointSystemRoosTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointSystemTransportDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointTransportConeComparisonDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointTransportStrictQuotient | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PointWeilHeartFlag | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleTateTwists | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProjectionFiniteReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperHeartBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperHeartBoundReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperOpenBoundaryZero | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperOpenCoefficientMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperOpenTowerComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurAdicReconstruction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityAffineLineOrientation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityAffineLineSupportStalk | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityChernClasses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityConventions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityCoprojection | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityDiagonalSectionPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityDivisorClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityExteriorProductFrame | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFiniteKummerLevel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFrameClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFrameIndependence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFrameKummer | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityFramePrincipalBoundary | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityGysinStructure | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityRankOneLocalCalculation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityRelativeKummer | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PuritySourceTransports | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.PurityTwistCancellation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QbarTwistCommonStage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QcqsCompactSupportRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QlbarDirectImageComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalLocalizedHom | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalStalkExact | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RealWeights | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RefinementExchangeCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RegularImmersionCancellation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RegularImmersionClassData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RegularImmersionExteriorClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RegularImmersionPurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RelativeSupportBottomDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RelativeSupportCoordinateModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ResidueControlledFiniteHoms | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RestrictionLocal | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementClopen | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementConstruction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementCore | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RingedRefinementFinite | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ScalarExchangeConstituents | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ScalarModelImmersionExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SectionCentredChartData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SectionLocalComparisonData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SectionLocalDualizingComparisons | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SemilinearFieldOperationLifts | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfBidualityClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfCommonStageDirectImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfProEtaleProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SignedTwistReductionComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SitePerfectCoefficientDual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SitePerfectDualizableHom | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SixFunctorDatum | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SixFunctorDualNotation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SixFunctorOperationDatum | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SixFunctorOperationDatumStages | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityMap | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityQbar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityTowerBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityTowerClasses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SmoothTrace | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.StratifiedConstantModelProductBound | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.StratifiedLatticeRank | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedAffineLineHomotopy | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedClassGeometry | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedExteriorShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedHomCocycleNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedHomPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SupportedTwistPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SystemClopenTensorCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SystemOperationExchangeRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.SystemTensorMateArrows | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TameRootTowerExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TateTwistLisseLine | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TateTwistLocallyFree | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TensorAdjunctionExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassChern | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassCoefficients | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassDiagonal | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassFinite | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassFiniteDiagonal | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassProjective | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassSystems | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerClassTwisting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceBaseChangeFirst | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceBaseChangeSecond | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFixedScheme | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaAdicSystem | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TraceGraphCorrespondence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TrfDevissageGeneration | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TrfWitnessedOpenPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TwConventions | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TwFrobeniusAction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UnboundedProperOpenInterchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UniformConstructibleExt | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UniformConstructibleExtRational | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorBundlePurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorBundleThomClass | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorPurityBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorPurityDirectSum | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorPurityFiniteReduction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorPurityNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VectorPurityScalarSingle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.VerdierExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilCompactSupportCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilInternalHomWeil | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WeilTateTwistFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WfTateTwist | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WfTateTwistCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ZlFrameworkOpenExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Paper.ZlShriekComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.BoundaryDualityInput | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CompactCoefficientComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CompositionProjectionMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FieldTensor | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteDualizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralSystemOperations | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.InternalHomPullback | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenFactorPullModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenFactorTensorModel | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.RationalOperations | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.RationalVerdier | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Targets.PoincareTateBoundedConstructible | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Targets.PoincareUncurry | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Targets.SmoothPurityQbar | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.Targets.VectorBundlePurity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| TargetsCheck | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.PoincareDuality.Poincare | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.PoincareDuality.Verdier | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.SmoothPurity.Defs | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Basic | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not edited | Transitive consumer; public interface of the direct consumer is unchanged. |

## Status

landed 20261021T225232-L-3803112 2026-10-21 (merge of deliver/W2/Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective)
