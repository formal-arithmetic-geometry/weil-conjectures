# CategoryTheory.Mod.preservesKFlatQuasiIso

## Reason

The preflight treats every changed instance body as an interface change, even for a
Prop-valued instance with the same signature. This record documents completion of the
proof, not a change to the mathematical statement. A local `omit ... in` for a private
helper is additionally classified as a command change; it has no scope outside that
private helper. All helpers are private and proved. The additional import is proof-only.

## Old

```lean
instance preservesKFlatQuasiIso : (extendScalars φ).PreservesKFlatQuasiIso :=
  sorry
```

## New

```lean
instance preservesKFlatQuasiIso : (extendScalars φ).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa
    ((comap φ).obj (regular S))
  have hl := ht.of_iso
    ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight ((comap φ).obj (regular S))) _).app K).symm
  have hf := hl.map (forget R)
  have he : (((extendScalars φ ⋙ forget S).mapHomologicalComplex _).obj K).Acyclic :=
    hf.of_iso ((NatIso.mapHomologicalComplex (extendForgetTensorIso φ) _).app K).symm
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ (forget S)).1 (he n)
```

## Users

The read-only `tools/downstream.py ... --uses CategoryTheory.Mod.preservesKFlatQuasiIso`
reported 47 downstream modules and only the item itself as a textual user of the exact
name. All downstream modules are listed conservatively below. Their statements keep the
same meaning because neither any signature nor any data definition was changed. No
consumer is edited, so no forced adaptation or consumer claim is required. The unchanged
instance proves the same proposition, and proof irrelevance applies to its value.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars | F2 | Instance proof completed; signature and visibility identical. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.AdicCompletionReduction | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CompletionMap | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedPointBasisEvaluation | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.IntrinsicKoszulCompletion | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.KoszulQuotientLimit | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Paper.ProfinitePointPullback | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.RingTheory.BoundedWContractibleExtension | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| Sheaf.Topology.BoundedExtremallyDisconnectedCover | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| TargetsCheck | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | not queried; unchanged consumer | No adaptation: instance signature, visibility, and proposition unchanged. |

## Status

landed 20261015T154209-L-164000 2026-10-15 (merge of deliver/F2/WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars)
