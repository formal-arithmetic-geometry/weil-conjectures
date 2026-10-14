# CupDerivedHomologyTensor

## Reason

Restore the derived-homology tensor interface removed by the earlier red-batch withdrawal
and prove its existence from the current landed dependency interfaces. Preserve the existing
localized-cycle class definition and every target statement.

## Old

The module contains only `cupLocalizedCycleClass`; the pairing structure and its existence
theorem are absent from the current base.

## New

Restore the public structure `CupDerivedHomologyTensor` with its bilinear `pair`, `natural`,
and `on_cycles` fields, and the proved theorem
`theorem exists_cupDerivedHomologyTensor : Nonempty (CupDerivedHomologyTensor k)`.
The existing localized-cycle definition has the identical signature and construction.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupDerivedHomologyTensor | S4 | restores and proves the pairing interface |
| Sheaf.Paper.ModuleCupDerivedClassComparison | unclaimed | imports `cupLocalizedCycleClass` from this module |

No consumer module is adapted. The two dependency modules are retained exactly as currently
landed and are not changed by this delivery.

## Status

landed 20261014T004113-L-2838542 2026-10-14 (merge of deliver/S4/Sheaf.Paper.ModuleCupDerivedHomologyTensor)
