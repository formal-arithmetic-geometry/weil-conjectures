# Sheaf.RingTheory.WeakEtaleRefinementProperties imports

## Reason

Remove the redundant direct public import of `Sheaf.RingTheory.IndPrincipalZariski`.
The unchanged `public import Sheaf.RingTheory.WeakEtaleRefinement` already exposes that
module through its own `public import Sheaf.RingTheory.IndPrincipalZariski`. This is an
import cleanup: every previously exposed declaration, instance, notation, definition,
and statement remains exposed by the same transitive public import closure. No theorem
signature or definition changes, no target meaning changes, and no adaptation is needed.
The preflight requests a change record for every removed public import even when redundant.

## Old

```lean
public import Sheaf.RingTheory.WeakEtaleRefinement
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
```

## New

```lean
public import Sheaf.RingTheory.WeakEtaleRefinement
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
```

The first imported module retains its public import of `IndPrincipalZariski`.
The other import edits in this delivery concern proof-only imports, as reported in
`report.md`; none is an adaptation of any downstream module.

## Users

The read-only command `python3 tools/downstream.py
Sheaf.RingTheory.WeakEtaleRefinementProperties` lists the following 29 transitive users.
Their statements keep the same meanings because all definitions and the public import
closure are unchanged. Group holders are the local coordination snapshot at second reading.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CompletionMap | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| Sheaf.RingTheory.WContractibleGeometricCriterion | F4 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| TargetsCheck | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Identical public import closure via WeakEtaleRefinement; no statement or proof adaptation. |

The sole direct importer, `Sheaf.RingTheory.WContractibleGeometricCriterion`, also publicly
imports `Sheaf.RingTheory.IndPrincipalZariski` itself. Its complete source was read; no
changed interface is required by its statements or its proof. No adapted module is delivered.

## Status

landed 20261015T154212-L-164807 2026-10-15 (merge of deliver/G1/Sheaf.RingTheory.WeakEtaleRefinementProperties)
