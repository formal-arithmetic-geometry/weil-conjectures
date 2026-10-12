# AlgebraicGeometry.eventually_isClosedImmersion_of_isLimit

## Reason

Prune unused proof infrastructure. The given limiting cone and Mathlib's section eventual-vanishing
lemma suffice, so the module no longer exports the independent limit-existence module. The original
public theorem signature and visibility are identical. No definitions or theorem statements change.
The repair imports the existing `Scheme.Hom.appLE_congr_hom` theorem privately and
removes its duplicate local helper; the four proof calls use the existing theorem.
No other module is edited. The direct consumer imports this module privately and does not use the
removed limit-existence declarations; indirect consumers therefore see the same interface.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EventuallyAffine
import Sheaf.Paper.DirectedColimitBaseChangeElementwise
```

The public theorem signature was:
```lean
theorem eventually_isClosedImmersion_of_isLimit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)] (h : D ⟶ (Functor.const Iᵒᵖ).obj T) [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)] (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T) (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsClosedImmersion f] : ∃ i : I, ∀ j : I, i ≤ j → IsClosedImmersion (h.app (op j))
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EventuallyAffine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
```

The public theorem signature is identical:
```lean
theorem eventually_isClosedImmersion_of_isLimit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)] (h : D ⟶ (Functor.const Iᵒᵖ).obj T) [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)] (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T) (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsClosedImmersion f] : ∃ i : I, ∀ j : I, i ≤ j → IsClosedImmersion (h.app (op j))
```

## Users

The table lists all transitive users returned by tools/downstream.py. The only direct importer is
Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope. No adaptations are required. Its unchanged source compiled against the
sandbox's freshly emitted modified module, confirming that the removed public import is unused.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleFiniteTypeClosedFibreStage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperClosedFibreApproximation | R1 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope | unclaimed | Direct importer: theorem signature unchanged; removed limit-existence declarations unused. |
| Sheaf.AlgebraicGeometry.ProperLimitNoetherian | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperLimitNoetherianCore | T2 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| TargetsCheck | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | B3 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Gabber | M1 | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Indirect importer: no statement changes; target module is imported privately by its direct consumer. |

## Status

landed 20261012T144123-L-2099932 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.EventuallyClosedImmersion)
