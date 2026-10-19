# AlgebraicGeometry.Scheme.exists_functorial_bounded_flat_replacement

## Reason

The stage-3 preflight requests a change record because the proof adds scoped commands
(`variable`, `open`, local notation and local instance attributes), as well as private
proved helpers for a functorial flat cover. These commands occur inside `section FlatCover`,
which ends before the existing public theorems. This record documents that diagnostic.
The public theorem signatures and public imports are identical to the original module.
No existing definition or target meaning changes. No consumer is adapted.

## Old

The flat-cover section and its three private helpers were absent. The existing signatures
were exactly:

```lean
theorem exists_functorial_bounded_flat_replacement
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (N : ℤ) :
    ∃ (Φ : ObjectProperty.FullSubcategory
        (fun K : CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ ↦ K.IsStrictlyLE N) ⥤
        CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ)
      (ε : Φ ⟶ ObjectProperty.ι _),
      ∀ F, (Φ.obj F).IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)) ((Φ.obj F).X i)) ∧
        QuasiIso (ε.app F) ∧ (∀ i : ℤ, Epi ((ε.app F).f i))

theorem exists_bounded_flat_replacement_zmod
    (T : Scheme.{u}) (n : ℤ) (N : ℤ)
    (F : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
    [F.IsStrictlyLE N] :
    ∃ (P : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
      (q : P ⟶ F), P.IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))) (P.X i)) ∧ QuasiIso q
```

## New

The same two signatures above remain verbatim; their proofs are now complete. The new
scoped commands are:

```lean
section FlatCover

universe v w r
variable {C : Type w} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

open CategoryTheory.Functor MonoidalCategory SheafOfModules

set_option hygiene false in
local notation "O" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{r} O

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory
```

The following private helper signatures use those local abbreviations. All their proofs
are complete, and the isomorphism definition is an explicit composition of the adjunction
counit and monoidal functor comparisons, with no arbitrary witness chosen from existence:

```lean
private theorem tensorPreadditive_boundedFlat : MonoidalPreadditive A

private noncomputable def tensorSheafificationIso_boundedFlat
    (F : PresheafOfModules.{r} (O).obj) :
    tensorRight ((PresheafOfModules.sheafification.{r} (𝟙 (O).obj)).obj F) ≅
      (SheafOfModules.forget.{r} O ⋙
        PresheafOfModules.restrictScalars (𝟙 (O).obj)) ⋙ tensorRight F ⋙
        PresheafOfModules.sheafification.{r} (𝟙 (O).obj)

private theorem existsFlatCover_boundedFlat :
    ∃ (T : A ⥤ A) (π : T ⟶ 𝟭 A),
      (∀ M : A, ObjectProperty.flat (T.obj M)) ∧ (∀ M : A, Epi (π.app M))
```

`end FlatCover` restores the surrounding scope before either public theorem is declared.
No private helper occurs in a public signature or public definition. Proof imports stay
non-public. Consequently all existing consumer statements and definitions retain their
meaning, and no target-statement review is reopened.

## Users

`tools/downstream.py Sheaf.Paper.BoundedFlatReplacement --uses` was run for each public
theorem. Only the item itself mentions either theorem name; the other modules inherit the
module through imports. The table includes every transitive consumer returned by
`tools/downstream.py Sheaf.Paper.BoundedFlatReplacement --names`, with holders read at
preparation time. This is a source-level interface check: all pre-existing public signature
text and public imports are unchanged; the added helpers are private and the added commands
are section-local. No consumer compilation repair is required or included.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.BoundedFlatReplacement` | T5 | Two proofs completed; private helper section added. |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectTorWindow` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` | V4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance` | G6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | G1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | Y6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedSupportStratumHom` | D3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CoherentExtVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen` | X3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ComparisonTorInterval` | H5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` | E3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | X2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | D4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` | A9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport` | T7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula` | H1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula` | R9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence` | H8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` | G3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | T8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | T9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | H9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethGlobalSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethMapAgrees` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization` | J6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenProductExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | S8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | A7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal` | U7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | B5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction` | M1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | W8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenSiteTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | X7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfEtaleExchanges` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfFullcdUsedClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange` | Y6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationStabilityLocus` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportLongExact` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportQuotientFlat` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductQuotientModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | J4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.CategoryTheory.SiteTorIntervalRestriction` | M7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.KunnethOneProper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | V5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicClosedConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AdicTorFlatCohomology` | S6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AmbientIndDerivedSums` | F5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AmbientIndDerivedTriangulated` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.AmplificationProper` | P6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ArbitraryFieldAdjunctionScalars` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | K2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundedConstructibleHomFiniteness` | H5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BoundedSiteAdjunctionTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | E1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CanonicalWeilFundamentalRepresentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CartesianCoefficientTwists` | Q4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CartesianCoefficients` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ClosedSupportConstructible` | N4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientChangeDualizing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentHom` | E4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentLisse` | F1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeart` | X8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartClosure` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartCommonStratification` | F2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartFiltration` | P4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartGeneration` | P7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartSmall` | F3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientHeartTriangulated` | Y5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTwistsDetailed` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactFiberStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportDirectImageTriangulated` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportReductionTower` | F8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportSiteCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | T9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ComparisonPullbackExact` | K3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedProjectionCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CompositeIntegrationCounit` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConcentratedComplexShift` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | Z5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantWeilStructure` | Z6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstantWeilStructureStageIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | U7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactnessBounded` | R4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompleteBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | Z7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleExtContinuity` | U8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleFlatCohomologyTorBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleHomContinuityDevissage` | P8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | R2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | Z8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DenseOpenPiOneSurjective` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | T2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DerivedGeometricStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DetIndHeartIISums` | C5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerLimit` | G3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DiagonalTowerSystem` | H4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | J2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImageCtfOpenTor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImageTorAmplitude` | H2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DirectImagesConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | S1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | F8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleDerivedScalarTensor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | N1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleGeometricBiduality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleSectionDeformationComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleWeilFundamentalRepresentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.EtaleWeilSheafEquivalence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | S4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ExternalRHomConePairing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | Q5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | G7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | G8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportConstructibility` | G9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteExtensionProperBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFieldExceptionalPreservation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | U3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeHomComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperBaseChange` | U4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | V9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionConstructibility` | V2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteRingCompactSupportProjectionMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | V3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | A4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | W2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStageDirectImageTorAmplitude` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTateSiteDescent` | V9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorInternalHomAnyField` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindow` | W5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | C1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | C7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupport` | Q9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupportII` | M2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FormalClosedSupportIILimits` | W6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FourierAdicArtinSchreier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | A2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | J3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFiberFiniteExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFiberQbar` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndConstructibleExtensions` | K4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndConstructibleFilteredColimits` | M1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartCanonicalPresentation` | W8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartFullFaithfulness` | M2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartIIVanishing` | E9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IndHeartKernelsCokernels` | M3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | W7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | W3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | C2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleCompactness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | J9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralExtensionByZero` | A3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | C3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLineTensorComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | H2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModelSurjectiveClosedReflection` | S3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModels` | D4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModelsOperations` | N1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | B4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorShriek` | F2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalar` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalarCanonical` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwists` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | C3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | C4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IsomorphismReductionTower` | N4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.KunBcKunnethCompat` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LevelwiseAdicTruncations` | S9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | H9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | J5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | D7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.MixedWeightsStability` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.NearbyCycleSheafFiniteness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | P2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OpenExtensionFiniteTor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | X5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PointFibreEquivalence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PointSectionsTensorShift` | Q1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PreservationConstructible` | B5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleCompositionTowerNormalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleTateTwists` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | P2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | K5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | G2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundTorsion` | J4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | Q3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | K6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperOpenCoefficientMate` | X5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperOpenCoefficientRefinement` | S5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | U2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | F8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PsiGoodOrientedCohomologyStrata` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | B7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | K7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineChartBounds` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityComparisonUnitInjectiveModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityConventions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | R2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDivisorClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDncComparisons` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDncFiniteRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFiniteExceptionalComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFiniteKummerLevel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFrameClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFrameKummer` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityFramePrincipalBoundary` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarAffineSupportBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarDerivedDirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarIdempotentComplete` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarOrdinaryAdjunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarProperBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QbarTwistCommonStage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | D3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | C1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | K8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalSliceCompletedEvaluation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalThickEvaluation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RationalizationIdempotentComplete` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RealBoundaryPathIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RealSheafSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RefinementCoefficientMate` | X6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | R3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | E1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | V2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfDirectImageCTFNonproper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfExchanges` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | K9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfPreservationClass` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | X7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothExceptionalBaseChangeStatement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothExceptionalPreservation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothMateCounitCancellation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | S6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.StandingExceptionalComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.StratifiedLatticeRank` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.StratumScalarExtension` | W2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.StrictWeilDualTate` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCohomologyHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCup` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedCupFunctoriality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedHomAdjunctionTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | K1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistLocallyFree` | S7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TensorTraceTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TopologicalStratifiedLisseLattices` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeFirst` | E1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceExceptionalAdmissibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraceTransposeBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.TwistPreservesFiniteness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | K3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UnboundedLocalizingPullback` | Y7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | X9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | K4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | M4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorPurityBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorPurityDirectSum` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorPurityFiniteReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorPurityNormalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VectorPurityScalarSingle` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | D8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilComplexQbarIdempotentComplete` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilIndSheafCategory` | D9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.WeilVerdierPreservationStrata` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | C3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.DirectImageScalarExchange` | E5 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | U9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarExchange` | S1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` | S8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImageComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | F3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | G1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.WeilTwistRationalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | M1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | Z9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | H6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.EtaleHomThickLocus` | S2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.EtaleInternalHomDevissage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.EtaleOpenTensor` | E6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FieldTensor` | N1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCompactProetale` | A2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FlatModel` | A3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FlatModelGeneration` | S3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | E3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | E7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GeoCartierCoeffExtension` | Z8 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | M7 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | N4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | T3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | G9 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | T4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | F4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | B4 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | U1 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Targets.PoincareTateBoundedConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.Targets.VectorBundlePurity` | F6 | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.StableCurveDiagramNoetherianModel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.StableModificationConstructibility` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.StableModificationSpreading` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.TwoTermPerfectDeterminant` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Trace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Convolution` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Unit` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.UnitVanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.ArtinSchreierCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Composition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.PointBiduality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RationalStage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.Localization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtension` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.Finiteness` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.Localization` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.SixOperations` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Statements and definitions unchanged; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Statements and definitions unchanged; no adaptation. |

## Status

landed 20261019T005428-L-2769545 2026-10-19 (merge of deliver/T5/Sheaf.Paper.BoundedFlatReplacement)
