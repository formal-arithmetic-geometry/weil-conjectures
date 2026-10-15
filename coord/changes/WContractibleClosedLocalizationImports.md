# WContractibleClosedLocalization redundant faithfully-flat import

## Reason

The second reader independently compiled the complete proof without the direct public
import `Mathlib.RingTheory.RingHom.FaithfullyFlat`. It remains publicly reachable by
this unchanged path (every edge was read in the source):

`Sheaf.RingTheory.IndPrincipalZariski` →
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` →
`Mathlib.AlgebraicGeometry.Morphisms.Flat` →
`Mathlib.RingTheory.RingHom.FaithfullyFlat`.

Removing this redundant edge preserves all publicly reachable declarations and
instances. Both existing declaration signatures and the complete family definition
remain byte-for-byte unchanged. No target meaning changes and no adaptation is needed.

## Old

```lean
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
```

## New

```lean
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Sites.Proetale
```

## Users

Enumerated all transitive importers with
`python3 tools/downstream.py Sheaf.RingTheory.WContractibleClosedLocalization`.
The same public path remains for every user; no existing statement or definition
changes meaning. Holders below are the local claim snapshot at second reading.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Unchanged public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Unchanged public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Unchanged public closure; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Unchanged public closure; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged public closure; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged public closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged public closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Unchanged public closure; no adaptation. |

## Status

landed 20261015T182202-L-784999 2026-10-15 (merge of deliver/D4/Sheaf.RingTheory.WContractibleClosedLocalization)
