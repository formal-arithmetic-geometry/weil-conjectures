# AlgebraicGeometry.Scheme.fixedPunctureDeck

## Reason

Repair reviewer X-e9fd4 point 4. The old definition restricts Spec(rho(zeta inverse)).
For the splitting field of X^3-2 over Q, with G=S3 and g=1, the resulting label
maps are a(zeta,sigma)=zeta inverse * sigma. They obey the reverse multiplication
law; zeta=(12), xi=(23), sigma=1 contradict the claimed left-action law.
The corrected definition restricts Spec(rho(zeta)) instead. Contravariance and
precomposition then give the forward label law required by the unchanged theorem.
Source: Stacks Project, Tag 03SF, finite Galois covers and permutation sets.

## Old

```lean
noncomputable def fixedPunctureDeck (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) ⟶
      (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) :=
  (Spec.map (CommRingCat.ofHom (ρ ζ⁻¹).toRingHom)).resLE
    (PrimeSpectrum.basicOpen (algebraMap H C h))
    (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
    change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
      PrimeSpectrum.basicOpen ((ρ ζ⁻¹) (algebraMap H C h))
    rw [AlgHom.commutes])
```

## New

```lean
noncomputable def fixedPunctureDeck (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) ⟶
      (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) :=
  (Spec.map (CommRingCat.ofHom (ρ ζ).toRingHom)).resLE
    (PrimeSpectrum.basicOpen (algebraMap H C h))
    (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
    change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
      PrimeSpectrum.basicOpen ((ρ ζ) (algebraMap H C h))
    rw [AlgHom.commutes])
```

All public signatures and visibility stay identical. The base compatibility proof
uses (rho zeta).commutes. The private deck multiplication equation is now
v(a*b)=v(a) followed by v(b). The reverse-law diagnostic is removed and its
connected-summand proof, with forward multiplication, is the public law proof.
The definition of fixedPunctureLabel changes through its call to fixedPunctureDeck;
its formula and signature otherwise stay identical. Consequently the underlying
function of fixedPunctureDescentAction now is a genuine left action, without sorry.

## Users

The complete transitive source-import closure below comes from tools/downstream.py.
Only the three modules marked as direct semantic users mention the public law or
action. No external user mentions the deck or label definitions themselves.
The corrected label at zeta is the old label at zeta inverse. Inversion is a
bijection, so orbit sets are unchanged; an element fixes a label precisely when
its inverse does, so stabilizer subgroups and their invariant subalgebras are
unchanged. Orbit descent therefore retains its conclusion and mathematical meaning.
The equivariant function algebra's equation rho(zeta)(f(i))=f(a(zeta,i)) now uses
the correct action: precomposing the section by Spec(rho(zeta)) pulls its coordinate
back by rho(zeta). This corrects the convention without changing the descended cover.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction` | E3 | definition convention corrected; left-action law proved; all signatures unchanged |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent` | K4 | direct semantic user: left action now agrees with coefficient equivariance; unchanged source compiles |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric` | unclaimed | direct semantic user: hD specifies corrected action; same orbit/stabilizer quotient; unchanged source compiles |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorOrbitComponentDescent` | unclaimed | direct semantic user: same orbit/stabilizer hypotheses and invariant-ring conclusion; unchanged source compiles |
| `Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitStrictLocalOrbits` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootOrbitDescent` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `TargetsCheck` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | transitive proof dependency only; no changed definition in its statement; no adaptation required |

No forced adaptations: the three direct users and the two intervening descent
modules compile unchanged against the corrected module in the sandbox overlay.
No other module is included in the delivery.

Affected targets are the declarations in Curve.FieldExtension (targets 3 and 4),
ProjectiveLine.GeometricStalk (target 1), and ProjectiveLine (target 2). Their
statements do not mention fixedPunctureDeck, fixedPunctureLabel, or the descent action,
and do not change their meaning. Their source files are compiled unchanged with
the corrected overlay. Target 5 in BaseChangeProperty is outside this module's
transitive import closure. Challenge.lean is untouched. No target statement needs
a semantic change or a weakening; the global build remains the maintainer's check.

## Status

landed 20261014T001716-L-2548680 2026-10-14 (merge of deliver/E3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction)
