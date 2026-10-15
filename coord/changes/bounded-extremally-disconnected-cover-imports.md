# Imports of Sheaf.Topology.BoundedExtremallyDisconnectedCover

## Reason

Remove the unused `MorphismDefs` public import, which is unrelated to the topology statement.
Retain the three public imports supplying the statement's topology and cardinal declarations.
Add `Mathlib.Topology.Category.Stonean.Basic` privately for the proof. No declaration signature,
visibility, definition, or target meaning changes. No consumer is adapted.

## Old

```lean
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.SetTheory.Cardinal.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

## New

```lean
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.Topology.Category.Stonean.Basic
```

## Users

Snapshot from `tools/downstream.py Sheaf.Topology.BoundedExtremallyDisconnectedCover --names`.
Claim holders are the local claim snapshot; no modules below are modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CompletionMap | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | Direct proof-only importer; checked unchanged against the new module. |
| TargetsCheck | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer; theorem signature and public definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Transitive importer; theorem signature and public definitions unchanged. |

## Status

landed 20261015T154212-L-164702 2026-10-15 (merge of deliver/F4/Sheaf.Topology.BoundedExtremallyDisconnectedCover)
