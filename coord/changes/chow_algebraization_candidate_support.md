# AlgebraicGeometry.chow_algebraization_candidate_support

## Reason

The former arbitrary-algebraization statement is false: for A=Q[[t]], I=(t), Z=Y=Spec Q((t)), q=identity, G=0, and F=O_Y, completion is zero but F has nonproper support. Stacks 088E proves proper support only for the candidate restricted from its proper compactification. This correction retains that compactification and the closed-fibre support containment, then proves boundary avoidance and proper support. The original target signatures and all definitions stay unchanged; no target semantics are affected. The sole actual user ChowAlgebraizationCore has its proof forced to obtain construction data while retaining its exact signature and visibility. The new construction statement is existential, and its witnesses are eliminated only in a theorem proof; no data definition chooses an unproved witness.

## Old

```lean
theorem chow_algebraization_candidate_support (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (Q : Z.IdealSheafData) (hQ : Q = (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) (G : CoherentFormalModule Z Q) (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0))) (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y) (hF : Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅ formalCompletionSystem (Q.comap q) F.obj)) : Scheme.Modules.HasSupportProperOver (q ≫ f) F.obj
```

## New

```lean
theorem chow_algebraization_candidate_support (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A] {P Y : Scheme.{u}} [IsLocallyNoetherian P] (p : P ⟶ Spec (.of A)) [IsProper p] (j : Y ⟶ P) [IsOpenImmersion j] (F' : CoherentModules P) (F : CoherentModules Y) (eF : (Scheme.Modules.tensorPullback j).obj F'.obj ≅ F.obj) (hSupport : {x : P | ¬ Subsingleton (F'.obj.presheaf.stalk x)} ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ Set.range j) : Scheme.Modules.HasSupportProperOver (j ≫ p) F.obj
```

## Users

The source-only downstream inventory has 201 modules. Only ChowAlgebraizationCore mentions the theorem outside its own module. All are listed below to record that no other signatures, statements or definitions change. The adapted core changes only the candidate import and the final proof lines. New module Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData returns the compactification construction before boundary removal.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | Signature unchanged; forced import and proof adaptation to obtain compactification data. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreSupport | G1 | Held statement corrected to the source support argument. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraLift | P2 | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | P2 | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| TargetsCheck | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration uses the changed support theorem; all existing statements and definitions are unchanged. |

## Status

landed 20261013T024033-L-3334100 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreSupport)
