# Algebra.exists_profinite_component_ring_pullback — redundant public import

## Reason

Remove the unused direct public import `Mathlib.AlgebraicGeometry.Scheme` while proving
`Sheaf.RingTheory.ProfiniteComponentRingPullback`. No scheme object occurs in the
statement or proof. The first dry run required a change record for this import change.
The two proof-only source imports that became unnecessary are also removed, and the
existing construction is imported privately.

This changes no definition, declaration signature, visibility, target statement or
elaborated type. In particular it does not change target meaning and requires no target
statement review. All declarations exported by the removed direct public import remain
publicly available through the retained path:

`Sheaf.RingTheory.IndPrincipalZariski` →
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale` →
`Mathlib.AlgebraicGeometry.Limits` → `Mathlib.AlgebraicGeometry.AffineScheme` →
`Mathlib.AlgebraicGeometry.Restrict` → `Mathlib.AlgebraicGeometry.Over` →
`Mathlib.AlgebraicGeometry.Scheme`.

Every edge of this path was checked to be a `public import`. Hence no downstream
adaptation is needed. Only the item module, held by D4, is edited.

## Old

Original imports, verbatim:

```lean
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.ClosedComponentSpectrumRestriction
import Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
```

## New

Delivered imports, verbatim:

```lean
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso
import WeilConjectures.RingTheory.ProEtale.WContractible
```

## Users

`python3 tools/downstream.py Sheaf.RingTheory.ProfiniteComponentRingPullback --uses
Algebra.exists_profinite_component_ring_pullback` lists the following 30 downstream
modules. No downstream source mentions the theorem name in code; the item's signature
is unchanged. The public import path above preserves Scheme availability for all users.
Group holders are the repository's claim records at the second reading.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover | B3 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover | C4 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CompletionMap | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.RingTheory.BoundedWContractibleExtension | D3 | Direct importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.RingTheory.WContractibleGeometricCriterion | F4 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| Sheaf.RingTheory.WLocalStalkIsomorphismRetraction | F4 | Direct importer; no change of statements or available Scheme declarations; no adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Transitive importer; no change of statements or available Scheme declarations; no adaptation. |

## Status

landed 20261015T154203-L-161716 2026-10-15 (merge of deliver/D4/Sheaf.RingTheory.ProfiniteComponentRingPullback)
