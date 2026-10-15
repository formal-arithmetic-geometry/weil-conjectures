# RetainedLocalizationProperties redundant Scheme import

## Reason

The second reader found that `Mathlib.AlgebraicGeometry.Scheme` is unused as a direct
import. The statement uses ring spectra and canonical quotient maps, not scheme objects.
The module is already publicly reachable by this unchanged chain:

`Sheaf.RingTheory.RetainedLocalization` → `Sheaf.RingTheory.PrincipalWLocalization` →
`Sheaf.RingTheory.IndPrincipalZariski` →
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale` →
`Mathlib.AlgebraicGeometry.Limits` → `Mathlib.AlgebraicGeometry.AffineScheme` →
`Mathlib.AlgebraicGeometry.Restrict` → `Mathlib.AlgebraicGeometry.Over` →
`Mathlib.AlgebraicGeometry.Scheme`.

Removing the redundant direct edge preserves every publicly reachable declaration and
instance. Both existing declaration signatures and the structural-map definition are
byte-for-byte unchanged. No target definition or statement changes meaning.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Scheme
```

## New

The direct import is removed. The unchanged public import of
`Sheaf.RingTheory.RetainedLocalization` supplies the same public module closure.

## Users

All transitive importers in the source import graph were enumerated. None needs adaptation;
the unchanged path above supplies `Scheme` to each one. Holders are the local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | Unaffected: the same public import closure remains. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CompletionMap | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | Unaffected: the same public import closure remains. |
| Sheaf.RingTheory.StrictWCoverProperties | F3 | Unaffected: the same public import closure remains. |
| Sheaf.RingTheory.WContractibleGeometricCriterion | F4 | Unaffected: the same public import closure remains. |
| Sheaf.RingTheory.WeakEtaleRefinement | unclaimed | Unaffected: the same public import closure remains. |
| Sheaf.RingTheory.WeakEtaleRefinementProperties | G1 | Unaffected: the same public import closure remains. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unaffected: the same public import closure remains. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Unaffected: the same public import closure remains. |

## Status

landed 20261015T154205-L-162574 2026-10-15 (merge of deliver/E1/Sheaf.RingTheory.RetainedLocalizationProperties)
