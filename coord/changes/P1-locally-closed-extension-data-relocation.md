# AlgebraicGeometry.Scheme.LocallyClosedExtensionData

## Reason

Move the existing module-sheaf data and its coherence predicate into
`Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence`. The geometric existence
lemma must precede the derived-category construction, so it cannot import the original
module that proves that construction. The original module publicly imports the new one.
The extracted declarations are byte-identical, including their docstrings and instance
attributes; this is a relocation, with no signature or body change. `DerivedCoherence`
and `locallyClosedExtensionCoherence` stay in their original module with their exact types.
No target meaning changes.

The moved declarations are `LocallyClosedCoefficients`, `LocallyClosedCoefficientImmersion`,
its `identity`, `comp`, `pull`, `push`, `pullComp`, `LocallyClosedExtensionData`, and its
`derived`, `closedOpenFactorization`, `openClosedFactorization`, `factorizationComparison`
and `Coherent`. The additional `NormalizedComposition` predicate copies the four composition
fields of `Coherent`; it does not replace or weaken that existing predicate. Full
faithfulness and its Hom-bijection field are constructed in the importing module.

## Old

In `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`:

```lean
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (openAdjunction a ha).unit.app M ≫ (restriction a).hom.app M = 𝟙 M
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (restriction a).hom.app M = a.pull.map ((closedComparison a ha).hom.app M) ≫
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit.app M
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)
```

## New

In `Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence`, publicly reexported
by the old module:

```lean
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (openAdjunction a ha).unit.app M ≫ (restriction a).hom.app M = 𝟙 M
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (restriction a).hom.app M = a.pull.map ((closedComparison a ha).hom.app M) ≫
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit.app M
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)
```

The other moved declarations listed above are also verbatim; their original names,
universes, binders, visibility, attributes and constructions are preserved.

## Users

The full transitive `tools/downstream.py` query finds 448 downstream modules.
Its `--uses` query matches declaration-name suffixes such as `comp`, `pull` and
`Coherent`, so it over-approximates actual uses. Every textual user is listed below,
including incidental matches. All moved declarations retain their names, types, bodies,
attributes and public visibility through the original module. No user's statement,
definition or proof needs adaptation. The unchanged direct consumer
`FiniteDualityLocallyClosedComparison` compiles against this interface. Holders below
are read from project claim records at packet preparation; no other group's file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Unchanged direct consumer; compiled successfully against the relocated data. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | P1 | Constructs module and derived coherence from the re-exported data. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Textual matches `derived`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Textual matches `comp`, `identity`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Textual matches `identity`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Textual matches `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Textual matches `comp`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Textual matches `derived`, `identity`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Textual matches `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FiniteWindow | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Textual matches `comp`, `derived`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.IntegralModels | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Textual matches `comp`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Textual matches `comp`, `identity`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassChern | unclaimed | Textual matches `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Textual matches `comp`, `derived`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Textual matches `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TwConventions | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.VerdierExchange | unclaimed | Textual matches `comp`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Textual matches `comp`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Textual matches `comp`, `pullComp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Textual matches `pull`, `pullComp`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Textual matches `derived`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Textual matches `derived`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Textual matches `comp`, `derived`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FlatModelGeneration | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Textual matches `pull`, `pullComp`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Textual matches `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Textual matches `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Textual matches `comp`, `identity`, `pull`, `pullComp`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Textual matches `comp`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Textual matches `comp`, `identity`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Textual matches `comp`, `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Textual matches `pull`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Textual matches `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Textual matches `Coherent`, `LocallyClosedCoefficientImmersion`, `LocallyClosedCoefficients`, `LocallyClosedExtensionData`, `comp`, `derived`, `pull`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Textual matches `comp`, `identity`, `pull`, `pullComp`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Textual matches `pull`, `pullComp`, `push`; unchanged declarations and re-export preserve its interface. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| WeilConjectures | unclaimed | Textual matches `Coherent`; unchanged declarations and re-export preserve its interface. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Textual matches `comp`; unchanged declarations and re-export preserve its interface. |
| Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence | new P1 module | Owns the unchanged definitions and the geometric assertion. |

## Status

landed 20261020T221304-L-4169280 2026-10-20 (merge of deliver/P1/Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence)
