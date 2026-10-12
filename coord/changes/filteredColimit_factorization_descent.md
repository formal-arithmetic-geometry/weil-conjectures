# filteredColimit_factorization_descent and import pruning

## Reason

Replace the rejected all-in-one factorization-data restatement by the strictly narrower
finite-data descent step of Stacks 0FWT. The new statement assumes neither stage henselianity
nor radical containment and does not assert that the colimit is henselian. The target now
proves the union ideal and radical statements, lifts at a henselian stage, and maps back.
No existing declaration signature or definition changes.

The unused public import of WeilConjectures.Mathlib.RingTheory.Henselian is removed.
The sole direct importer, Sheaf.RingTheory.HenselizationColimit, imports the target module
only for proofs and independently imports WeilConjectures.Mathlib.RingTheory.Henselian.
Thus the removed import remains available there and through every transitive importer.
No downstream module requires adaptation and no target meaning changes.

## Old

No finite-data descent declaration existed in the repository. The target module had:

```lean
public import WeilConjectures.Mathlib.RingTheory.Henselian
```

## New

The above unused public import is removed. Proof-only dependencies are plain imports:

```lean
import Sheaf.RingTheory.FilteredColimitFactorizationDescent
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
```

The new declaration, in its own module, has signature:

```lean
theorem filteredColimit_factorization_descent
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (I : Ideal (colimit F : CommRingCat.{u}))
    (hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i)
    (f : (colimit F : CommRingCat.{u})[X]) (hf : f.Monic)
    (g₀ h₀ : ((colimit F : CommRingCat.{u}) ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfact : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ (i : Λ) (fᵢ gᵢ hᵢ : (F.obj i)[X]),
      fᵢ.Monic ∧ gᵢ.Monic ∧ hᵢ.Monic ∧ fᵢ.map (colimit.ι F i).hom = f ∧
      IsCoprime (gᵢ.map (Ideal.Quotient.mk (J i))) (hᵢ.map (Ideal.Quotient.mk (J i))) ∧
      fᵢ.map (Ideal.Quotient.mk (J i)) =
        gᵢ.map (Ideal.Quotient.mk (J i)) * hᵢ.map (Ideal.Quotient.mk (J i)) ∧
      (gᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = g₀ ∧
      (hᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = h₀
```

## Users

`tools/downstream.py Sheaf.RingTheory.FilteredColimitHenselianPair --uses
filteredColimit_henselianPair` reports 162 transitive importers and no use of the target
name outside its own declaration. The sole direct importer's whole source was read;
its independent Henselian import preserves availability for all downstream proofs.
The new descent declaration is used only by the target proof, not by its signature.
The following rows list the transitive importers from the read-only repository snapshot;
claim holders are that snapshot's records, and no held file is modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FilteredColimitHenselianPair | B2 | proof uses the new finite-data theorem; signature unchanged |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | C2 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | D2 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | N1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | H1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | Q2 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | J1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | K1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | C1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| Sheaf.RingTheory.HenselizationColimit | F2 | unchanged statements; independent Henselian import at HenselizationColimit |
| TargetsCheck | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | T2 | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X2 | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | K1 | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged statements; independent Henselian import at HenselizationColimit |

## Status

landed 20261012T063504-L-3152655 2026-10-12 (merge of deliver/B2/Sheaf.RingTheory.FilteredColimitHenselianPair)
