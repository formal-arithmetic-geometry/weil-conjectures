# CommAlgCat.filteredColimit_tensorProduct_elementwise and universal

## Reason

Repair reviewer X-ba5ef, point 4. The index category must be small relative to the
stage-algebra universe. For independent universes an oversized filtered system of
fields can have zero as its colimit among small algebras, falsifying both statements.
Use `uI` for the stage algebras in both open declarations. The ring-hom declaration,
all definitions, all target statements, and all downstream signatures stay unchanged.

## Old

```lean
theorem filteredColimit_tensorProduct_elementwise
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N] :
    (∀ (x : (colimit F : CommAlgCat R) ⊗[R] N),
      ∃ (i : I) (t : (F.obj i : Type vA) ⊗[R] N),
        LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = x) ∧
    (∀ (i : I) (t : (F.obj i : Type vA) ⊗[R] N),
      LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = 0 →
        ∃ (j : I) (u : i ⟶ j),
          LinearMap.rTensor N (F.map u).hom.toLinearMap t = 0)

theorem filteredColimit_tensorProduct_universal
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N]
    (M : Type uM) [AddCommGroup M] [Module R M]
    (μ : ∀ i : I, (F.obj i : Type vA) ⊗[R] N →ₗ[R] M)
    (hμ : ∀ (i j : I) (u : i ⟶ j),
      (μ j).comp (LinearMap.rTensor N (F.map u).hom.toLinearMap) = μ i) :
    ∃! l : (colimit F : CommAlgCat R) ⊗[R] N →ₗ[R] M,
      ∀ i : I, l.comp (LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap) = μ i
```

## New

```lean
theorem filteredColimit_tensorProduct_elementwise
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uI, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N] :
    (∀ (x : (colimit F : CommAlgCat R) ⊗[R] N),
      ∃ (i : I) (t : (F.obj i : Type uI) ⊗[R] N),
        LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = x) ∧
    (∀ (i : I) (t : (F.obj i : Type uI) ⊗[R] N),
      LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = 0 →
        ∃ (j : I) (u : i ⟶ j),
          LinearMap.rTensor N (F.map u).hom.toLinearMap t = 0)

theorem filteredColimit_tensorProduct_universal
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uI, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N]
    (M : Type uM) [AddCommGroup M] [Module R M]
    (μ : ∀ i : I, (F.obj i : Type uI) ⊗[R] N →ₗ[R] M)
    (hμ : ∀ (i j : I) (u : i ⟶ j),
      (μ j).comp (LinearMap.rTensor N (F.map u).hom.toLinearMap) = μ i) :
    ∃! l : (colimit F : CommAlgCat R) ⊗[R] N →ₗ[R] M,
      ∀ i : I, l.comp (LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap) = μ i
```

## Users

The following is the full transitive downstream list from `tools/downstream.py`.
Only the two fibre modules call the corrected elementwise theorem; neither calls
the universal theorem. Their index and algebra universes already coincide.
The remaining modules only depend transitively on these proofs: no statements or
definitions change, and no target statement needs a definition review.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.RingTheory.FilteredEtaleFiberSeparableImage | unclaimed | Direct caller; same universe already; compile unchanged against correction. |
| Sheaf.RingTheory.FilteredEtaleFiberStructure | unclaimed | Direct caller; same universe already; compile unchanged against correction. |
| Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.RingTheory.HenselizationPairGRing | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.RingTheory.HenselizationPairGRingCore | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.RingTheory.PairHenselizationFiberLocalization | K3 | Transitive proof dependency only; statement and interface unchanged. |
| Sheaf.RingTheory.PairHenselizationRegularFibers | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| TargetsCheck | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | S2 | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive proof dependency only; statement and interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive proof dependency only; statement and interface unchanged. |

## Status

landed 20261012T194153-L-469153 2026-10-12 (merge of deliver/W2/Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise)
