# AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar

## Reason

The only hole in the assigned module asserted preservation of arbitrary K-flat complexes.
That assertion was used only to supply quasi-isomorphism preservation for the pullback
and to compute its derived factorization. Both uses have shorter proofs because the
coefficient morphism is an isomorphism and both factors are exact. No downstream module
mentions the retired instance, and the class `Functor.PreservesKFlatComplexes` and all its
proved generic APIs are retained. This is pruning of an unnecessary obligation, not a proof
of its stronger assertion.

## Old

```lean
instance preservesKFlatComplexes_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesKFlatComplexes := sorry
```

`preservesKFlatQuasiIso_upperStar` used `Functor.preservesKFlatQuasiIso_comp` and
`leftDerivedUpperStarIso` used `Functor.leftDerivedFunctorCompMapDerivedCategoryIso`,
both requiring that instance.

## New

The unused `preservesKFlatComplexes_mapMod_upperStar` declaration is removed, with no
replacement statement or hole. `preservesKFlatQuasiIso_upperStar` uses exactness directly.
The signature of `leftDerivedUpperStarIso` is unchanged. Its proof installs left exactness
of extension of scalars by `Mod.extendScalarsIsoComapInv`, applies
`Functor.leftDerivedFunctorCompIso`, then whisks
`Functor.leftDerivedFunctorIsoMapDerivedCategory` for `mapMod(f^*)` by the derived extension
of scalars. No target signature or definition of coefficients, categories, or operations changes.
Docstrings are updated to explain this route.

## Users

`tools/downstream.py` lists the following transitive importers. Its `--uses` search and a
whole-library search show that the retired name occurs only in its own module. In particular,
no downstream proposition changes meaning and no consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse | B2 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CompletionMap | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | No use of the retired instance; existing signatures unchanged. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | No use of the retired instance; existing signatures unchanged. |
| Sheaf.Topology.BoundedExtremallyDisconnectedCover | F4 | No use of the retired instance; existing signatures unchanged. |
| TargetsCheck | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | E4 | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | A2 | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | E4 | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | No use of the retired instance; existing signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No use of the retired instance; existing signatures unchanged. |

## Status

landed 20261015T161024-L-260015 2026-10-15 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar)
