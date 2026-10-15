# Algebra.isIndPrincipalZariski_of_bijective_localRingHom

## Reason

Prove the theorem, prune unused imports, and add scope commands needed for the
proved helpers. The delivery checker requires a record for removing a public
import and adding `open` commands. No existing declaration changes signature,
visibility, or mathematical meaning. No module besides the item is adapted.

The removed public import `Mathlib.GroupTheory.MonoidLocalization.Away` remains
publicly reachable through the retained `Sheaf.RingTheory.IndPrincipalZariski`:

`Sheaf.RingTheory.IndPrincipalZariski` → `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` → `WeilConjectures.Mathlib.RingTheory.Etale.Weakly` → `Mathlib.RingTheory.Localization.BaseChange` → `Mathlib.RingTheory.Localization.Away.Basic` → `Mathlib.GroupTheory.MonoidLocalization.Away`

Thus its removal changes no importer-visible declaration. The two direct
importers are `Sheaf.RingTheory.WeakEtaleRefinementProperties` and
`Sheaf.RingTheory.ProfiniteComponentRingPullback`; all transitive importers listed
below retain the same statements. The added commands only resolve notation and
names inside this module; they introduce no declarations or instances.

## Old

```lean
theorem isIndPrincipalZariski_of_bijective_localRingHom
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]
    (hlocal : ∀ (q : Ideal B) [q.IsPrime],
      Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :
    IsIndPrincipalZariski A B
```

Public import removed:

```lean
public import Mathlib.GroupTheory.MonoidLocalization.Away
```

## New

The theorem signature is unchanged:

```lean
theorem isIndPrincipalZariski_of_bijective_localRingHom
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]
    (hlocal : ∀ (q : Ideal B) [q.IsPrime],
      Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :
    IsIndPrincipalZariski A B
```

The redundant public import is omitted. Added scope commands:

```lean
open CategoryTheory CategoryTheory.Limits
```

Inside `namespace Algebra`:

```lean
open scoped BigOperators
```

The proof imports removed and added are listed in `report.md`. Every new helper
is private and proved. No definition changes, so no target meaning is reopened.

## Users

`tools/downstream.py Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso --uses
Algebra.isIndPrincipalZariski_of_bijective_localRingHom` listed the following
transitive importers; no downstream source mentions the public theorem yet.
Claim holders were read from the local coordination snapshot.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` | C3 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover` | B3 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | C2 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` | C3 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover` | C4 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | C1 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.RingTheory.BoundedWContractibleExtension` | D3 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.RingTheory.ProfiniteComponentRingPullback` | D4 | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.RingTheory.WContractibleGeometricCriterion` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.RingTheory.WLocalStalkIsomorphismRetraction` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `Sheaf.RingTheory.WeakEtaleRefinementProperties` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `TargetsCheck` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No semantic change; declarations and public dependency closure retained. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | A2 | No semantic change; declarations and public dependency closure retained. |

## Status

landed 20261015T154203-L-161575 2026-10-15 (merge of deliver/D4/Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso)
