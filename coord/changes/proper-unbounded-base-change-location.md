# AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring

## Reason

The objectwise projection-formula proof needs the existing unbounded proper base-change
statement. Importing its old module creates a cycle through ProjectiveLine, Gabber,
restricted derived sections, Derived.Shift, UpperShriek, and the projection-formula parent.
The dry run reported that cycle even though the pinned local compiled library accepted
the import. Proper is unclaimed in the local claim snapshot, so the user-authorized
unclaimed-module adaptation exception applies. Move just the unchanged unbounded theorem
to a lower-level statement module and publicly re-export it from its original module.
The bounded-below theorems and their proof imports stay in Proper.

## Old

Module: `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`.

```lean
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry
```

## New

Module: `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.
The old module adds `public import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.
The declaration keeps exactly its original name, binders, conclusion and public visibility.
Its old hole is moved, not duplicated; its docstring now supplies the named node and full
natural-language proof. No definition or target statement changes meaning.

```lean
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  sorry
```

## Users

Local claim snapshot; all import descendants and declaration users from
`tools/downstream.py --uses` are listed. No downstream signature requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Publicly imports the new module; removes only the relocated theorem body. No declaration is weakened or renamed. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | C2 | Uses a proof-only import of the relocated theorem, breaking the cycle. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | New module holding the unchanged declaration and its existing hole. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No edit: original public name and theorem signature remain available through Proper. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No edit: original public name and theorem signature remain available through Proper. |

## Status

landed 20261014T194627-L-1482207 2026-10-14 (merge of deliver/C2/Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise)
