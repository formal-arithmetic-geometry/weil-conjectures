# AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker

## Reason

Repair the returned retirement of the standalone duplicate. The entire cokernel
calculation is retained as local hc of pic_proper_ntorsion, with the parent
signature unchanged. The former empty stub did not expose the command API needed
by the imported axiom probe; the repaired stub exports Mathlib.Lean.Linter as a
public meta import. It declares no mathematical object or theorem.

## Old

```lean
theorem Scheme.Hom.pic_proper_ntorsion_coker
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n))
```

The parent imported PicProperNTorsionCoker and used:
```lean
  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
```

## New

The standalone declaration is retired. Its module is a declaration-free stub
with public meta import Mathlib.Lean.Linter so the maintainer's imported probe
can elaborate run_cmd. The parent removes the retired import, adds proof-only
imports PicardDecomposition and Mathlib.Algebra.Group.TypeTags.Hom, and uses a
typed local hc block containing the former complete proof. The cokernel node's
lean record points to the surviving parent's second conjunct. The parent node's
proof dependencies point directly to decomposition and divisibility rather than
the retired component. No target statement or mathematical definition changes.

The original parent against the delivered stub fails at line 70 with:
```text
Unknown constant AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker
```
The adapted parent compiles. The stub passes the isolated imported batch probe.
The parent is checked with the delivery tool's appended declaration probe.
The 2026-10-14 10:02 UTC return requires the unrelated imported-probe collision
repairs to be withdrawn from this delivery; those six module edits and their
change record are therefore omitted. Their existing collisions are not repaired
by this cokernel retirement.

## Users

Source search and tools/downstream.py --uses found the parent as the sole direct
caller/importer. The table includes every transitive importer for completeness.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Forced adaptation: inline the complete cokernel proof and replace its proof imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | P4 | Retire the duplicate; retain only the verification meta import. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| TargetsCheck | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same mathematical definitions and surviving signatures; no source adaptation needed. |

## Status

landed 20261014T103112-L-1343484 2026-10-14 (merge of deliver/P4/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
