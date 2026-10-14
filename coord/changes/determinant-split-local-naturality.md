# determinant_split_comparison_local

## Reason

Return X-59b54 rejected the strengthened local theorem because its full conclusion
is already stated by determinant_split_comparison_exists. No Lean caller uses the
local declaration. Retire it and map new-determinant-split-local to the canonical
existing declaration, which includes naturality. Importing that theorem here would
create a cycle: its module imports this one for the restriction-transfer theorem.
That transfer theorem remains unchanged, so no adaptation or cycle is needed.

## Old

```lean
theorem determinant_split_comparison_local {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))
```

## New

The unused declaration above is removed. The DAG node now uses the existing
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists` in
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison`:

```lean
theorem determinant_split_comparison_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
              (homOfLE hZW).op y))
```

## Users

`tools/downstream.py --uses determinant_split_comparison_local` finds no downstream
callers. A full `rg` search finds only the declaration being retired. The 328 transitive importers are
listed below for completeness. No definition or target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal | M1 | Retire unused duplicate; keep restriction theorem unchanged. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | H1 | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | Y3 | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| TargetsCheck | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No use of the changed declaration; statement and proof unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No use of the changed declaration; statement and proof unchanged. |

## Status

landed 20261014T035544-L-887375 2026-10-14 (merge of deliver/M1/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)
