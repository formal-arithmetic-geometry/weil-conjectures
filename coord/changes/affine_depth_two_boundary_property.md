# AlgebraicGeometry.Scheme.affine_depth_two_boundary_property

## Reason

Reviewer X-7ea0b, head 7ea0b4e99, requires a structural double-dual repair. The arbitrary coherent-H theorem is false: A=k[x,y,z], W=D(x) union D(y), H=tilde(A/(x)). At (x,y), the structure stalk has depth two but H has depth one. The corrected theorem applies to the actual finite double dual.

## Old

```lean
theorem affine_depth_two_boundary_property
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (H : (Spec A).Modules) (hqc : H.IsQuasicoherent)
    (hfin : ∀ V : (Spec A).Opens, IsAffineOpen V →
      Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) :
    ∀ x : Spec A, x ∉ W →
      ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)
```

## New

```lean
theorem affine_depth_two_boundary_property
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∀ x : Spec A, x ∉ W →
      ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x)
```

## Users

The table lists every transitive downstream module and both direct users returned by tools/downstream.py --uses. No target type or definition changes. AffineDepthTwoLocallyFreeModel is unclaimed in the repository snapshot. Its original proof fails against this changed helper; only necessary proof imports and the witness construction/application are adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel | unclaimed | Forced proof adaptation: construct the double dual, prove finiteness and restriction preservation, then apply helper. Signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesTestFiniteExtensionFlat | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| TargetsCheck | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive user only: unchanged statements, definitions, and proofs; caller interface unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoBoundaryProperty | E1 | Owned helper: signature corrected to the actual finite double-dual sheaf. |

## Status

landed 20261013T134800-L-129498 2026-10-13 (merge of deliver/E1/Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoBoundaryProperty)
