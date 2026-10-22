# AlgebraicGeometry.Etale.strictLocal_exchange_compatibility

## Reason

Retire coord/retire-items.tsv row 2900's duplicate Sheaf module. The current item has
zero sorry holes. Its theorem is already completely proved, and the adopted source
tree contains the same geometric compatibility identity in the full affine colimit
presentation. The small/full comparison is canonical, but the signatures are not
definitionally equal. A blind import substitution would change the schemes used by
both consumers. Instead each consumer now proves its original small-model formula
by affine germ hom-ext and unitSectionRestriction_comp, with the two small-model leg
projection equations. No new module or renamed duplicate theorem is introduced.

Source read: literature/stacks-project/etale-cohomology.tex, theorem-higher-direct-images
(Tag 03Q9), especially the affine-initiality and representative-to-limit maps, and
lemma-proper-base-change-f-star (Tag 0A3U), whose omitted compatibility is exactly the
representative calculation formalized here. Both the adopted and duplicate theorem
proofs, the node dependencies, and both full consumer proofs were read.

## Old

The withdrawn module publicly imported QcqsStrictLocalModuleComparison and BaseChange.Square
from WeilConjectures, plus Sheaf.EtaleUnitSectionRestriction and
Sheaf.SmallStrictLocalSectionMaps (all paths under AlgebraicGeometry except the square).
Its only public theorem was:

```lean
theorem strictLocal_exchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictHenselizationStructuralMap s))
    (hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g')
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
      unitSectionRestriction Λ
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u}
            (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
        ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j)
        (by
          change _ ≫ pullback.snd _ f =
            pullback.fst f (Scheme.strictHenselizationStructuralMap s)
          simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
            pullbackSymmetry_hom_comp_snd])) :
    let H := (upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
        (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      eqToHom (by rw [Category.id_comp]) ≫
      a ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
```

It also contained the unused, fully proved private module_inverseImage_stalk_germ.
Both consumers privately imported it and applied this theorem once. Their existing
public imports, public signatures, and all definition bodies are retained verbatim.

## New

The old file is listed in deleted.txt, and delivery replaces it by an empty module.
Its node is reattached to the unchanged existing source declaration:

```lean
theorem strictLocal_exchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictLocalization s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictLocalizationToBase s))
    (hqt : q ≫ pullback.snd f (Scheme.strictLocalizationToBase s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictLocalizationToBase s) = g')
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (ha : IsQcqsStrictLocalModuleComparison Λ f s F a) :
    let H := (upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
        (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      eqToHom (by rw [Category.id_comp]) ≫
      a ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictLocalizationToBase s)) g' hq.symm).inv.app F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
```

The node's statement explicitly records the full-colimit presentation. Its
statement_change retains the former statement and proof fields and audits both
parent citers. The adopted theorem, proof, attributes, public imports and private
imports are all unchanged. Its preserved proof still uses the adopted
StrictLocalSectionPullback; that dependency is retained.

In QcqsGeometricExchangeFactorization, the old specialized call is replaced by
colimit hom-ext on the initial affine representatives. The existing
exchange_pointed_representative, unitSectionRestriction_comp, and small-model
leg projections give the two representative composites. Substitution of he₀ and
associativity close the equation. GeometricFibreExchangeRepresentative is now an
explicit private proof import.

StrictHenselizationModuleFibreFactorization uses the same representative argument
inside hc′. The existing second half then extends to every pointed neighbourhood
using exchange_pointed_representative and cancels the isomorphism d.hom. The now
unused transportedIso_hom private helper and its local he are removed. None of its
constructed witnesses or statement changes. The two parent node proof routes
explicitly replace the retired-node dependency by these existing general lemmas.

## Users

The exact direct-import/name census found two consumers and no quarantined parent.
Both consumers were unclaimed in coord/claims in this snapshot. The whole transitive
import census has 840 modules. All non-direct consumers retain the same
public declarations, definitions, and public imports from their immediate dependencies.
No target statement or target definition changes, so target semantic review stays valid.
The sk-thm-iff unit's realized statement and proof node are unchanged, as is the
sk-lem-universal-datum unit. Only below-unit proof dependencies are replaced.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | D3 assignment | Withdraw the duplicate; attach its node to the adopted theorem. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | unclaimed | Private import and proof adapted; original public interface and definitions unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Private import and proof adapted; original public interface and definitions unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CartesianCoefficientTwists | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoordinateCounitArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteProjectionActionLaws | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteWindow | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerRefinement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperOpenTowerComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityConventions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalRealizationScalarCoherence | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RealWeights | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SectionCentredChartData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SectionLocalComparisonData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedHomPullback | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassChern | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TwConventions | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WfTateTwist | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | see current claim | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Not edited; consumer interfaces and mathematical meaning unchanged. |

## Status

landed 20261022T025319-L-1274304 2026-10-22 (merge of deliver/D3/Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility)
