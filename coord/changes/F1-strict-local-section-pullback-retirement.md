# AlgebraicGeometry.Etale.strictLocal_section_pullback

## Reason

Complete the zero-hole retirement at coord/retire-items.tsv row 2860, authorized by
coord/changes/retire-sheaf-twins-20261020.md. The old Sheaf theorem is already fully
proved, but duplicates the adopted-source theorem name with a different presentation:
the small ring-colimit strictHenselizationScheme versus the full strictLocalization.
The two are canonically isomorphic, not definitionally equal. An import substitution
alone would change the types required by the consumers.

Withdraw the old module and attach its node to the unchanged adopted-source theorem.
Preserve both consumer signatures and the body of strictLocalFibreRestriction verbatim.
Their proofs now apply the already proved, general unitSectionRestriction_comp directly.
The composite small limit leg has first projection f' followed by the marked point
(by hqt/hi', hpoint/ht and smallStrictHenselizationBaseChangeMap_fst) and second
projection g' (by hq/hi and smallStrictHenselizationBaseChangeMap_snd).
Two pullback extensionality steps identify its graph with geometricFibreSectionLift.
Expanding unitSectionRestriction gives the same representative equation, and the
existing terminal evaluation cancellation and exchange-colimit argument finish.

This preserves the small model in every existing consumer, without recreating the
retired theorem under another public or private name. No new declaration or hole,
no chosen data, no change to an upstream file or target, and no change to the unit
route is involved. The construction uses no nonempty or nonzero hypothesis: empty
schemes and zero coefficient modules satisfy the same universal-property equations.
The generic composition theorem and both projection lemmas were read with their
complete proofs. The source was read at etale-cohomology.tex theorem-higher-direct-images
(Tag 03Q9, lines 8015-8100) and lemma-proper-base-change-f-star (Tag 0A3U, lines
18282-18309): these are precisely canonical restriction maps and their compatibility,
not a new continuity or invertibility assertion.

## Old

The withdrawn module publicly imported:

- WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
- WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
- Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction
- Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps

It also privately imported WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence.
It declared four fully proved private helpers terminalEvaluation_eq_res_local,
terminal_pullback_formula, composite_unit, pre_composite_unit, and this public theorem:

```lean
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
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
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
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
          pullbackSymmetry_hom_comp_snd]) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)
```

The two direct consumers privately imported the withdrawn module and applied its
strictLocal_section_pullback once each. All their existing public imports are retained.

## New

The obsolete module is listed in deleted.txt and is represented as an empty module
by the delivery tool. Its node is attached to this existing adopted-source theorem,
whose source, proof, signature, attributes and imports are unchanged:

```lean
theorem strictLocal_section_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
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
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    qcqsStrictLocalSectionRestriction Λ f s F j ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictLocalizationToBase s)) g' hq.symm).inv.app F) =
      geometricFibreSectionRestriction Λ sq F
        ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)
```

The DAG statement and lean.statement record that full-model signature verbatim;
lean.note explains the presentation difference. statement_change preserves the old
statement/proof/dependencies and audits both parent citers. This records the authorized
change of formal presentation, not a weakening. The node's mathematical content
(canonical representative restriction) and statement dependencies are retained. Its proof records the preserved
adopted proof. Neither parent invokes this differently typed theorem: each now derives
its unchanged small-model equation from the general composition theorem. Their DAG
proof/proof_deps/proof_origin record the new route, removing only their dependence on
the retired small-model application. No blueprint unit statement or realized proof
step is bypassed (sk-thm-iff realizes lemma-weil-pbc-property-iff-acyclicity).

## Users

The direct-import and whole-library name census reports exactly two consumers:
Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility and
Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility. Both are unclaimed
in the source snapshot. Their signatures remain byte for byte identical, and the
latter's entire data definition is unchanged. Only their private import and theorem
proofs change; the fibre-compatibility proof paragraph is updated to match its proof.
No other public environment changes, since the old import was private in both files.
The full downstream census has 842 modules, recorded below as required by
brief-stage3 section 4. Non-direct users need no adaptation: the original signatures,
definitions and public imports of their dependencies are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | F1 assignment | Withdraw obsolete copy, keep adopted-source theorem. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | Q4 | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | unclaimed | Proof uses general unit restriction composition and the two small leg projections; signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | unclaimed | Proof uses general unit restriction composition and the two small leg projections; signature unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoordinateCounitArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteWindow | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerRefinement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperOpenTowerComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityConventions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RealWeights | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SectionCentredChartData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SectionLocalComparisonData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | P5 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedHomPullback | B8 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassChern | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TwConventions | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WfTateTwist | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C7 | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Not edited; public consumer interfaces unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Not edited; public consumer interfaces unchanged. |

The only parent DAG nodes are lem-weil-pbc-strict-local-exchange-compatibility and
lem-sbc-strict-local-fibre-restriction-compatibility. Both are updated in this packet.
A search of quarantine found no additional importer or declaration use. No DAG node
is deleted, no quarantine archive is deleted, and this retirement is not inferred
from having zero importers. The actual replacement arguments are in both consumers.

## Status

landed 20261022T021029-L-163874 2026-10-22 (merge of deliver/F1/Sheaf.AlgebraicGeometry.StrictLocalSectionPullback)
