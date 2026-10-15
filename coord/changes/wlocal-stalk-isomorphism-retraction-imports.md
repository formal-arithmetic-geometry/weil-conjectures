# WLocalStalkIsomorphismRetraction proof-only import

## Reason

`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` is used only to construct the local
`Module.FaithfullyFlat` instance in the proof. It is not needed by any public signature, so its
import is private as required by stage 3 import pruning. The module's declarations and all target
statements retain the same types.

## Old

```lean
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
```

## New

```lean
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CompletionMap | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.RingTheory.BoundedWContractibleExtension | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| Sheaf.RingTheory.WContractibleGeometricCriterion | unclaimed | Uses the proved target declaration; its statement is unchanged. |
| TargetsCheck | unclaimed | Target statement and imports remain unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Proof-only import visibility changes; declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Proof-only import visibility changes; declarations unchanged. |

## Status

landed 20261015T161025-L-260241 2026-10-15 (merge of deliver/F4/Sheaf.RingTheory.WLocalStalkIsomorphismRetraction)
