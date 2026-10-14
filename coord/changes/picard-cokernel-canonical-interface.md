# Scheme.Hom.pic_proper_ntorsion_coker

## Reason

Upstream review #1428 identifies this public cokernel theorem as a duplicate of the
second clause of `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` in upstream
`Curve/Jacobian.lean`. The cited module and declaration are absent from the pinned
source checkout, the project library, and its compiled imports. They do occur in the
upstream PR snapshot. This repair forward-ports that exact canonical public interface
into the held module, using the existing proved component theorems, and retires the
old public name. Its cokernel argument becomes a private, completely proved helper.
No object definition or target statement changes; the sole caller retains its exact
signature and public imports. No new sorry is introduced.

## Old

```lean
theorem Scheme.Hom.pic_proper_ntorsion_coker
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n))
```

## New

```lean
theorem Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [ConnectedSpace C]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (Additive C.Pic) n ≃+
        (Fin (2 * (C ↘ Spec (.of k)).genus) → ZMod n)) ∧
      Nonempty (Additive C.Pic ⧸ (zsmulAddGroupHom (α := Additive C.Pic) n).range ≃+
        ZMod n) ∧
      Function.Surjective fun L : picardZero k C ↦ L ^ n
```

`picQuotient` is a private proved helper with the old proposition. The new public
theorem has the upstream signature, including all three clauses. It is a theorem,
not an object selected from an existence assertion.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Forced proof adaptation: retired constant is unknown; same theorem signature and imports. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| TargetsCheck | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No adaptation: unchanged aggregate theorem signature; no use of retired declaration. |

The only adapted module is `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`
(unclaimed in the claim snapshot). Its original line 70 fails with
`Unknown constant AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` against
the delivered dependency. The replacement lines install the hypotheses of the
canonical theorem and convert its additive quotient clause to the original
multiplicative quotient. All other proof lines, imports, signatures and visibility
in that module stay unchanged. The source-original counterfactual compile failed;
the adapted module compiled against the same dependency overlay.

The canonical interface is now available through this Sheaf module rather than
upstream `Curve/Jacobian.lean`: when that newer upstream module is adopted, this
forward-port should be replaced by importing it and retaining the caller transport.

## Status

landed 20261014T033117-L-608548 2026-10-14 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
