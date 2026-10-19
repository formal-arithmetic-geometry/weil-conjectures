# AlgebraicGeometry.ProEtale.sfConstructibleExceptionalAdjointDischarge

## Reason

Preflight flags added section variables and scoped notation as an interface change.
This record documents their local scope. All added helper declarations are private.
The `FixedCounit` section ends before the original public theorem, so its variables
and scoped opening do not change the theorem or any importer. The new reassociation
lemma is generated from a private helper. No public definition, instance, notation,
theorem signature, universe, or public import changes. No target review is reopened.

## Old

The public signature, verbatim, was:

```lean
theorem sfConstructibleExceptionalAdjointDischarge
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    sfClassFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1))
        (2 * d) ∧
    ∃ eps : ∀ (L : DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
        (_hL : DerivedCategory.TStructure.t.plus L),
      (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L) ⟶ L,
      (∀ (L) (hL : DerivedCategory.TStructure.t.plus L) (K)
          (_hK : (DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
                X).mapDerivedCategory).essImage K),
        Function.Bijective (fun a : K ⟶
            (sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L ↦
          (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map a ≫
            eps L hL)) ∧
      ∀ (L L') (hL : DerivedCategory.TStructure.t.plus L)
          (hL' : DerivedCategory.TStructure.t.plus L') (a : L ⟶ L'),
        (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map
            ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).map a) ≫
              eps L' hL' = eps L hL ≫ a
```

Its proof was `by sorry`. There was no `FixedCounit` section.

## New

The public signature is identical, verbatim:

```lean
theorem sfConstructibleExceptionalAdjointDischarge
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    sfClassFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1))
        (2 * d) ∧
    ∃ eps : ∀ (L : DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
        (_hL : DerivedCategory.TStructure.t.plus L),
      (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L) ⟶ L,
      (∀ (L) (hL : DerivedCategory.TStructure.t.plus L) (K)
          (_hK : (DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
                X).mapDerivedCategory).essImage K),
        Function.Bijective (fun a : K ⟶
            (sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L ↦
          (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map a ≫
            eps L hL)) ∧
      ∀ (L L') (hL : DerivedCategory.TStructure.t.plus L)
          (hL' : DerivedCategory.TStructure.t.plus L') (a : L ⟶ L'),
        (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map
            ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).map a) ≫
              eps L' hL' = eps L hL ≫ a
```

The proof constructs the relative counit and proves the vanishing and Hom bijectivity.
The added commands, all inside `section FixedCounit`, are:

```lean
open scoped CategoryTheory.Functor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [CompactSpace Y] [QuasiCompact f]

variable [HasCompactification f]
```

`end FixedCounit` precedes the original public theorem. These commands supply only
local elaboration context for the private fixed adjunction, counit and proof lemmas.
The `@[reassoc]` attribute is applied only to the private counit naturality helper.
The direct proof-only imports are pruned as listed in report.md.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge --uses
AlgebraicGeometry.ProEtale.sfConstructibleExceptionalAdjointDischarge` reports
452 transitive importers, all listed below. Its textual declaration-use
search finds only the item itself. The public signature and public imports are
unchanged, and all new declarations are private, so no importer needs adaptation.
No other module is edited and no other group's claim is touched.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.InternalHomPullback | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperHeartBound | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityChernClasses | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalStalkExact | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.RestrictionLocal | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SfPreservationClass | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SmoothTrace | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TwConventions | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.VerdierExchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilOne | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not queried; not adapted | Same signature and meaning; no adaptation. |
| TargetsCheck | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.Statement | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not queried; not adapted | Same signature and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not queried; not adapted | Same signature and meaning; no adaptation. |

## Status

landed 20261019T112445-L-3941921 2026-10-19 (merge of deliver/E7/Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge)
