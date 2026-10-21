# AlgebraicGeometry.Scheme.OrderedExchange.reduction

## Reason

Keep the strict quotient construction and its universal derived counit together in
`DerivedReductionModelData`, so the K-flat computation law is available without repeatedly
unfolding a nested existential selection. The original choice of the pair had the same
universal property. No arbitrary object is selected from an unproved existence theorem:
`reductionData_exists` is proved, and its counit-compatible universal property determines
its result up to the unique isomorphism used by every downstream comparison.

Move the construction prefix to `Sheaf.Paper.ProEtaleConstantReductionModels`, publicly
reexported by the original module. The new chain-normalization lemma must refer to
`projection`, while the proof of `projection_isIso` must import that lemma. The prefix
module makes this dependency acyclic. This factorization follows the mathematical
construction/computation/invertibility dependency, and is not a split to avoid a compile
limit. All five files are compiled independently by the project tool.

The derived augmentation is the explicit universal lift. The proved
`augmentation_eq_choose` identifies it with selection from the original uniqueness
interface. Its stronger `augmentation_normalized` law holds on every complex. The
pullback-normalization predicate is the same displayed equation factored through the
generic `ModelPullNormalized`; its K-flat hypothesis is unchanged. No flat-term hypothesis
is added to that predicate or to `reductionPullIso_existsUnique`.

Every existing public signature and universe is preserved, including the generic
`completionMateComparison` alias. The original public imports are reexported through the
models module. No source-library file, target statement, or quarantined file changes.
The changes to definitions used downstream require the ordinary independent semantic
review: the coefficient ring is still the discrete constant ring, its quotient maps are
still `exchangeScalar ≫ d.projection`, and the unit, pullback comparison, projection mate,
and completion are the same universally normalized constructions, up to their prescribed
unique isomorphisms. In particular no completeness, boundedness, properness or flatness
assumption is inserted into the projection statement.

## Old

```lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T := (reduction_exists d T).choose
```

```lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reduction_exists d T).choose_spec.choose
```

```lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  AlgebraicGeometry.Scheme.reductionComplexCounit (reductionModule d T)
    (reduction d T) (reductionCounit d T) P
```

```lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  (augmentation_existsUnique d T).exists.choose
```

```lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ∀ P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d U).map
              ((proEtaleRingDerivedPullbackFactors f
                (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).hom.app P) ≫
            reductionComplexCounit d U
              (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeConstantPull (A := A) f).map (reductionComplexCounit d V P) ≫
            (exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
              (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f)
                (.up ℤ)).hom.app P)
```

## New

```lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T :=
  (reductionData d T).reduction
```

```lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reductionData d T).counit
```

```lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionData d T).complexCounit P
```

```lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  canonicalModelAugmentation (Functor.const ℕᵒᵖ) (reductionModule d T)
    (reductionData d T) (ordinaryAugmentation d T)
```

```lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ModelPullNormalized (reductionModule d V) (reductionModule d U)
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (reductionData d V) (reductionData d U) (ordinaryReductionPullIso d f) τ
```

The six new public model API declarations are `reductionData_exists`, `reductionData`,
`canonicalModelAugmentation`, `augmentation_normalized`, `augmentation_eq_choose`, and
`ModelPullNormalized`. The node `def-sp-constant-reduction-models` records them. Every
proof in the models module is complete. The definitions of ordinary scalar extension,
quotient transitions, the pullback mate and `projection` retain their existing bodies.
Local transparency attributes and proved private helpers support elaboration only.

## Users

`tools/downstream.py Sheaf.Paper.ProEtaleConstantReductionTower --uses ...` was run for
`reduction`, `reductionComplexCounit`, `augmentation`, and `ReductionPullNormalized`.
The two live downstream modules use the reexported APIs; the last three names have no
textual uses there. The `reduction` search also counts uses of the generic interface,
which remain unchanged. All quarantined importers listed in the earlier B3 change
record remain preserved; zero live importers is not used as a withdrawal argument.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleConstantReductionTower | T1 | Construction moved behind a public import; projection proof completed from the new finite computation route. |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | Original source compiles unchanged (10.1 s); no adaptation. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | Original import loading stops because the server lacks CompletionFiniteReduction.olean; no interface adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Quarantined original preserved; existing declarations and route retained. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Quarantined original preserved; existing interface retained. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Quarantined original preserved; existing interface retained. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Quarantined original preserved; existing interface retained. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Quarantined original preserved; existing interface retained. |


Current-main consumer inventory added after the repair preflight. The scan matches
short declaration names, so it over-approximates actual namespace-qualified uses.
All existing signatures and public names are preserved by the Models reexport.
No listed module is adapted. The six direct consumers compile unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CondensedERealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Textual downstream match; signatures publicly reexported; no adaptation. |

## Status

landed 20261021T061653-L-1809251 2026-10-21 (merge of deliver/T1/Sheaf.Paper.ProEtaleConstantReductionTower)
