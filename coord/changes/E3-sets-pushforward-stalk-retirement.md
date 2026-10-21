# AlgebraicGeometry.Scheme.strictHenselizationBaseChangeMap

## Reason

Retirement assignment in coord/retire-items.tsv and the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The duplicate Sheaf module contains zero
holes but collides with its official twin. The twin uses strictLocalizationToBase,
whereas existing consumers use the small-model strictHenselizationStructuralMap.
These schemes are canonically isomorphic, not definitionally equal. A bare import swap
would change the domain of the base-change leg and the section comparison.

## Old

The withdrawn module exported the following signatures (normalized whitespace):

```lean
theorem strictHenselizationBaseChange_condition {X Y : Scheme.{v}} (f : X ⟶ Y) {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) : (pullback.fst (strictHenselizationStructuralMap y) f ≫ (strictHenselizationCone y).π.app (op (op j)) ≫ Spec.map (ΓSpecIso ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left.unop).inv) ≫ ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom = pullback.snd (strictHenselizationStructuralMap y) f ≫ f

def strictHenselizationBaseChangeMap {X Y : Scheme.{v}} (f : X ⟶ Y) {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) : pullback (strictHenselizationStructuralMap y) f ⟶ pullback ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom f

def strictHenselizationSectionMap {X Y : Scheme.{v}} (f : X ⟶ Y) {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) : Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)) ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (strictHenselizationStructuralMap y) f)).obj ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1))

theorem sets_pushforward_stalk_strictHenselization {X Y : Scheme.{v}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (H : Sheaf X.smallEtaleTopology (Type (v + 1))) {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) : (∀ t : ((pointSmallEtale y).sheafFiber.obj (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)), ∃ (n : ObjectProperty.FullSubcategory (fun n : (pointSmallEtale y).fiber.Elements => IsAffine n.1.left)) (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj n.obj.1))), (pointSmallEtale y).toPresheafFiber n.obj.1 n.obj.2 (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H).obj s = t) ∧ ∃ Θ : ((pointSmallEtale y).sheafFiber.obj (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) → ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)))), (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))), Θ ((pointSmallEtale y).toPresheafFiber ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1) ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2 (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H).obj s) = ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.map (strictHenselizationSectionMap f y j).op (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (strictHenselizationStructuralMap y) f)) (Type (v + 1)) (X.smallGrothendieckTopology @Etale) ((pullback (strictHenselizationStructuralMap y) f).smallGrothendieckTopology @Etale)).unit.app H).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1))) s)) ∧ Function.Bijective Θ ∧ ∀ Θ' : ((pointSmallEtale y).sheafFiber.obj (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) → ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)))), (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))), Θ' ((pointSmallEtale y).toPresheafFiber ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1) ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2 (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H).obj s) = ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.map (strictHenselizationSectionMap f y j).op (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (strictHenselizationStructuralMap y) f)) (Type (v + 1)) (X.smallGrothendieckTopology @Etale) ((pullback (strictHenselizationStructuralMap y) f).smallGrothendieckTopology @Etale)).unit.app H).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1))) s)) → Θ' = Θ
```

## New

The DAG attachment points to the existing official module
WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization, with the
same declaration names. Its theorem uses strictLocalizationToBase and its affine
cone. No adopted source-library file is changed.

The following proved/concrete small-model adapter is new under Sheaf:

```lean
theorem smallStrictLocalization_toBase {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) : Spec.map (smallStrictHenselizationColimitIso s).inv ≫ strictLocalizationToBase s = strictHenselizationStructuralMap s

def smallStrictHenselizationBaseChangeMap {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) : pullback (strictHenselizationStructuralMap y) f ⟶ pullback ((AffineEtale.Spec Y).obj ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom f

theorem smallStrictHenselizationBaseChangeMap_snd {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) : smallStrictHenselizationBaseChangeMap f y j ≫ pullback.snd _ f = pullback.snd (strictHenselizationStructuralMap y) f

theorem smallStrictHenselizationBaseChangeMap_fst {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) : smallStrictHenselizationBaseChangeMap f y j ≫ pullback.fst _ f = pullback.fst (strictHenselizationStructuralMap y) f ≫ (strictHenselizationCone y).π.app (op (op j)) ≫ Spec.map (ΓSpecIso ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left.unop).inv

def smallStrictHenselizationSectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) : Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)) ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (strictHenselizationStructuralMap y) f)).obj ((MorphismProperty.Over.pullback @Etale ⊤ f).obj ((AffineEtale.Spec Y).obj ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1))
```

The new leg is marked irreducible, with a proved API for its two projections, so
consumers avoid expanding the full colimit/pullback construction. Explicit arguments
to the projection rewrite lemmas keep the final representative-pullback calculation
within the unchanged heartbeat and single-file time limits.

The new leg is pullback.map of Spec.map (smallStrictHenselizationColimitIso s).inv,
followed by the official strictHenselizationBaseChangeMap. It is not an independent
copy of that definition. The final-functor colimit coprojection formula proves the
map to the base and both projection formulas. The graph section is its pullback
lift with the identity.

All six adapted consumers were unclaimed when inspected. The five direct importers
use SmallStrictLocalSectionMaps; StrictLocalSectionPullback uses the same map through
QcqsStrictLocalModuleComparison. Public signatures replace the retired map name by
the transported map name. Both pullback projections coincide with the old concrete
leg, so pullback.hom_ext identifies the maps; hence the mathematical statements,
module comparison definitions, and representative formulas are preserved. The
strict-local definitions continue to use the small-model structural morphism.
The targets do not change text; this definition-transport equivalence is the semantic
check needed for targets that transitively use those definitions.

QcqsStrictLocalRestrictionBijective no longer invokes the retired small-model set
stalk theorem. Its proof computes the set stalk colimit and the explicit section
colimit using the existing cofilteredLimitSections theorem. It compares their
vertices by the unique colimit isomorphism and checks the given linear map agrees
on every component. No replacement public stalk theorem is introduced. The DAG
proof steps record this route. This retains the unit route and its continuity lemma.

## Users

The table lists every transitive importer reported by tools/downstream.py, plus the
retired item and new adapter. Unedited rows preserve their mathematical interfaces
through the equal transported leg; they require no source adaptation. All edited
existing consumers were unclaimed; holder entries on unedited modules are irrelevant
to this delivery because their files are not edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CartierKummerData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitIdentity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ExactCompactificationUnitRefinement | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.KunnethSupported | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSupportExchangeRange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ProperSurjectionEtaleSectionEqualizer | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.QcqsGeometricExchangeFactorization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | E3 | Withdraw duplicate; node attaches to official module. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps | new, E3 | Concrete transport through existing colimit isomorphism; projection proofs. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalSectionPullback | unclaimed | Use transported small-model maps; original mathematical statement preserved. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportLongExact | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.TowerCompositionRefinement | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AffineLineInvariance | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AmbTateRootProjectionReduction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AmbientIndDerivedSums | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CanonicalRingedRefinementShape | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CartesianCoefficientTwists | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CartesianCoefficients | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ClopenStrictSystemComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ClosedSupportConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientChangeDualizing | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientHeart | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientHeartFiltration | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientHeartGeneration | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactProductProperSupportLaws | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactProductRealizationLaws | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactProductTwistLaws | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportCoefficientAction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportFiniteAction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportReductionTower | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompleteCompactSupportProetale | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CompositeIntegrationCounit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CondensedBoundedHomContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleCompactness | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleExtContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoordinateCounitArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CoordinateGermConcentrationData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CtfHomCoefficientComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CtfHomConditionB | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.CtfHomLocalizationDevissage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DeltaProperPushforward | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DeltaRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DerivedGeometricStalk | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DerivedOpenSquareRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DetIndHeartIISums | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DiagonalTowerLimit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DiagonalTowerSystem | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DiagonalTowerTraceLimit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DirectImageChangeRingTranspose | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DirectImagesConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleCompactScalarCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.EtaleSumCoefficientComputation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FieldTwistInverse | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteExceptionalInternalHom | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteProjectionActionLaws | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteRingSectionDeformation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteTateSiteDescent | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteWindow | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteWindowBounded | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FiniteWindowUnbounded | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FormalClosedSupport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FormalClosedSupportII | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FormalClosedSupportIILimits | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndConstructibleExtensions | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndHeartFullFaithfulness | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndHeartIIVanishing | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IndHeartKernelsCokernels | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralConstantModelHeart | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralConstructibleExt | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralConstructibleHeart | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralHeartDualizable | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralHeartLocalModel | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralHeartRealizationExact | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralHeartResidueDual | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralIndConstructibleStability | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralIndHeartRealization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralIndLowerTail | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralLineDerivedComparisons | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralLinePowerComparisons | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralLineReductionDefinitions | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralLineReductionRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralLineRestrictions | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralModels | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralModelsOperations | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralQuotientCoefficients | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralQuotientProjectionMap | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralStratumExtBound | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralStratumHomFormula | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTensorProduct | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTensorPullback | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTwistBaseChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTwistDerivedScalar | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralTwistScalarCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntegralWindowCoproductComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.InternalHomDualConstructibleModels | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.KummerAdditivity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.LatticeSubquotientFiltration | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.LocalizedDirectImageComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.MixedReductionUnit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.NearbyProperHyperdescent | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.NormalizedCoefficientFamilies | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PbcCoefficientTwists | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProEtaleTateTwists | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperHeartBoundLattice | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperHeartBoundReduction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperOpenTowerComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityConventions | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityExteriorProductFrame | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityFiniteKummerLevel | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityFrameClass | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityFrameKummer | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityFramePrincipalBoundary | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.PurityRankOneLocalCalculation | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.QbarTwistCommonStage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.QlbarDirectImageComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalClosedSupportConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalLocalizedHom | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RealWeights | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RefinementExchangeCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementClopen | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementConstruction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementCore | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RingedRefinementFinite | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.ScalarModelImmersionExtension | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SectionCentredChartData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SectionExceptionalFibreCoherence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SectionLocalComparisonData | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SectionLocalDualizingComparisons | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SignedTwistReductionComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.StratifiedConstantModelProductBound | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.StratifiedLatticeRank | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedClassGeometry | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedClassSiteComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedCupFunctoriality | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedExteriorClassArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedExteriorClasses | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedExteriorShift | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedHomCocycleNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedHomPullback | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedTwistMultiplication | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SupportedTwistPullback | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.SystemTensorMateArrows | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.TateTwistLisseLine | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.TateTwistLocallyFree | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.TraceBaseChangeFirst | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.TwistPreservesFiniteness | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.UnboundedProperOpenInterchange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.UniformConstructibleExt | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.UniformConstructibleExtRational | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorBundlePurity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorPurityBaseChange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorPurityDirectSum | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorPurityFiniteReduction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorPurityNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.VectorPurityScalarSingle | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Paper.WeilCompactSupportCohomology | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.BoundaryDualityInput | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.FieldTensor | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralSystemOperations | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.OpenFactorPullModel | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.OpenFactorTensorModel | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Targets.PoincareTateBoundedConstructible | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.Targets.VectorBundlePurity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | not edited | Transitive consumer; equal projection formulas preserve definitions and statements. |

## Status

landed 20261021T183343-L-1605786 2026-10-21 (merge of deliver/E3/Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization)
