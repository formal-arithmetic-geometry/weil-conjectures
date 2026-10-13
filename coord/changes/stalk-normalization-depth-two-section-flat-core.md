# AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core

## Reason

The original statement is false, as recorded in its STATEMENT-DISPUTED comment:
the cone double cover has generic rank two and special fibre dimension three.
The returned repair restored the missing generic rational-section data, but its
statement then duplicated GaloisCover.stalk_normalization_depth_two_section_flat.
The caller imports the core, so importing that caller back would form a cycle.
Generalize the core in place to descent and openness for arbitrary finite p and
flat t meeting x, with flat pullback. This is a proved, reusable part of the
argument. The unchanged caller performs the formal-test calculation separately.
No definition or Challenge target changes. The general core is axiom-free.

## Old

```lean
theorem stalk_normalization_depth_two_section_flat_core {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∃ W : (pullback c a).Opens,
      τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ W ∧ Flat (n ∣_ W)
```

## New

```lean
theorem stalk_normalization_depth_two_section_flat_core
    {L E T : Scheme.{u}} [IsLocallyNoetherian L]
    (p : E ⟶ L) [IsFinite p] (t : T ⟶ L)
    [Flat t] [Flat (pullback.snd p t)] (x : L) (b : T) (hb : t b = x) :
    ∃ W : L.Opens, x ∈ W ∧ Flat (p ∣_ W)
```

## Users

The only direct declaration user is StalkNormalizationDepthTwoSectionFlat,
unclaimed in the holder snapshot. Its old line 118 fails against the new core
with an application type mismatch: hσ has type σ ≫ c = 𝟙 S but is expected to
have type ↥S. Its signature, visibility and public imports remain identical.
The necessary proof-only import StalkNormalizationSplitFormalTest and replacement
proof lines construct the local normalization and section, obtain the flat test,
transport coproduct flatness, establish local Noetherianity, and invoke the core.
The unchanged caller still states exactly the source's normalization conclusion.
The original fails and the adapted caller compiles against the same overlay.
All other modules only depend transitively on the unchanged caller interface.
The table is the current tools/downstream.py module list; no other adaptation is
needed. Removed core public imports are all still available to downstream users
through the caller's unchanged public imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlat | unclaimed | Signature unchanged; forced formal-test assembly in proof. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No direct use; caller interface unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No direct use; caller interface unchanged. |
| TargetsCheck | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No direct use; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No direct use; caller interface unchanged. |

## Status

landed 20261013T113340-L-3182609 2026-10-13 (merge of deliver/E4/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore)
