# AlgebraicGeometry.ProEtale.StrictTower.beta_evaluation

## Reason

The three postponed proper/open assertions are proved. The proof constructs a private
constant-ring coefficient equivalence and proves exact-localization and evaluation
coherence. Server preflight requires this record for the new private instances and
section commands, although all 18 existing public signatures and all canonical public
definitions remain identical. No consumer is edited.

## Old

The module had no declarations named `W_limits`, `W_colimits`,
`fixedRestriction_faithful`, `scalarUnit_injective`, `scalarUnit_surjective'`,
`fixedRestriction_full`, or `fixedRestriction_essSurj`. It had no `ExactMates` or
`EvaluationCoherence` sections. The affected public theorem signatures were:

```lean
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv B gU j' j g h)

theorem beta_evaluation [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Derived B U) (n : ℕ) :
    (ev B X' n).map ((beta B a j' j g h hsq).hom.app M) ≫
        (evalJ B j' n).hom.app ((G B a).obj M) ≫
        (moduleJ B j').mapDerivedCategory.map ((evalG B a n).hom.app M) =
      (evalG B g n).hom.app ((J B j).obj M) ≫
        (modulePullback B g).mapDerivedCategory.map ((evalJ B j n).hom.app M) ≫
        (singleBeta B a j' j g h hsq).hom.app ((ev B U n).obj M)

theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj B j).unit

theorem openToR_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToR B j)
```

The first, second and fourth proofs were `sorry`; the third was already proved.

## New

Those four public signatures are unchanged. The three holes are proved, and the
existing open-unit proof is shortened using the same coefficient equivalence.
All new helper declarations are private and proved. The new instance declarations
are recorded verbatim below:

```lean
private theorem W_limits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteLimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

private theorem W_colimits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteColimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

private theorem fixedRestriction_faithful (X : Scheme.{u}) :
    (fixedRestriction B X).Faithful where
  map_injective h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom) h) U) x

private theorem scalarUnit_injective (X : Scheme.{u}) :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
  rw [← Presheaf.isLocallyInjective_forget_iff]
  change Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
  infer_instance

private theorem scalarUnit_surjective' (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (scalarUnit B X) :=
  scalarUnit_surjective B X

private theorem fixedRestriction_full (X : Scheme.{u}) :
    (fixedRestriction B X).Full where
  map_surjective {M N} f := by
    let a : (PresheafOfModules.restrictScalars (scalarUnit B X)).obj M.val ⟶
        (PresheafOfModules.restrictScalars (scalarUnit B X)).obj N.val :=
      { app := f.hom.app
        naturality g := by ext x; exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let H := SheafOfModules.forget.{u + 1} R ⋙
      PresheafOfModules.restrictScalars.{u + 1} (scalarUnit B X)
    have : H.Full := inferInstance
    obtain ⟨b, hb⟩ := H.map_surjective a
    refine ⟨b, ?_⟩
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun t ↦ t.app U) hb) x

private theorem fixedRestriction_essSurj (X : Scheme.{u}) :
    (fixedRestriction B X).EssSurj where
  mem_essImage F := by
    let P := (fixedPresheaf B X).obj F.obj
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let M := (PresheafOfModules.sheafification.{u + 1} (R := R) (scalarUnit B X)).obj P
    let a := (PresheafOfModules.sheafificationAdjunction.{u + 1} (R := R)
      (scalarUnit B X)).unit.app P
    let f : F ⟶ (fixedRestriction B X).obj M :=
      ⟨{ app := a.app
         naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply a g x }⟩
    let H := sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
    have : IsIso (H.map f) := by
      have : IsIso ((sheafToPresheaf _ _).map (H.map f)) :=
        isIso_toSheafify _ (H.obj F).property
      exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
    have : IsIso f := isIso_of_reflects_iso _ H
    exact ⟨M, ⟨(asIso f).symm⟩⟩
```

These are private proof theorems, registered with `attribute [local instance]` only within this module. The two `W` registrations provide finite preservation
for pointwise functors; the other five concern the private scalar restriction.
Their registration can affect instance search, so it is included in independent
review. No new mathematical assumption or coefficient choice is introduced.
The new `variable` commands are enclosed in `ExactMates` and
`EvaluationCoherence`; those section variables do not escape. The private
`exactAdj`, square constructors and categorical transport helpers supply typed
interfaces so the proofs do not repeatedly unfold coefficient sheaf data.
The module-level elaboration setting respects declared transparency for this
purpose; scalar full faithfulness, scalar essential surjectivity and the
section-specific scalar calculation keep explicit overrides where typeclass
resolution needs the sheafification presentation.

## Users

The source audit ran `tools/downstream.py
Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows --uses W_limits W_colimits
fixedRestriction_faithful scalarUnit_injective scalarUnit_surjective'
fixedRestriction_full fixedRestriction_essSurj`. Every new instance name has zero
textual users in the shared source. The transitive import closure contains
570 modules, listed below. Their existing statements keep exactly the
same meaning because the public signatures, definitions and public imports do
not change. The proof instances add no data to their signatures. No forced
adaptation is needed. Holders are read from the shared claim snapshot with the
six-hour expiration policy of SETUP.md; this record makes no claim on consumers.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` | Y9 | three holes proved; private proof helpers added |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | P4 | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | D2 | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | U5 | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | S3 | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | unclaimed | unchanged; no adaptation |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | U2 | unchanged; no adaptation |
| `Sheaf.CategoryTheory.FilteredDerivedOperationLifts` | unclaimed | unchanged; no adaptation |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | unchanged; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | unchanged; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | unchanged; no adaptation |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | unchanged; no adaptation |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | unchanged; no adaptation |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CanonicalRingedRefinementShape` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CanonicalRingedRefinementSquare` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportSiteCoherence` | U4 | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompleteCompactSupportProetale` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteProjectionActionLaws` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | M3 | unchanged; no adaptation |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperOpenTowerComparison` | H1 | unchanged; no adaptation |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RefinementExchangeCoherence` | H4 | unchanged; no adaptation |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementClopen` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementCoefficientSquare` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementConstruction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementCore` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementData` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.RingedRefinementFinite` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ScalarExtensionTensorUnit` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SmoothTrace` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.SystemTensorMateArrows` | H8 | unchanged; no adaptation |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassChern` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TwConventions` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.VerdierExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | unchanged; no adaptation |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | unchanged; no adaptation |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | S4 | unchanged; no adaptation |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | unchanged; no adaptation |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | unchanged; no adaptation |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | unchanged; no adaptation |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | unchanged; no adaptation |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | unchanged; no adaptation |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | unchanged; no adaptation |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | unchanged; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | unchanged; no adaptation |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | unchanged; no adaptation |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | unchanged; no adaptation |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | unchanged; no adaptation |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | unchanged; no adaptation |
| `TargetsCheck` | unclaimed | unchanged; no adaptation |
| `WeilConjectures` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | unchanged; no adaptation |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | unchanged; no adaptation |

## Status

landed 20261020T211910-L-3516620 2026-10-20 (merge of deliver/Y9/Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows)
