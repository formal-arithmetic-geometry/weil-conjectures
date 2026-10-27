# CategoryTheory.BigradedExactCouple.finiteCocone_limits

## Reason

Restore the module quarantined by the 2026-10-23 upstream sync. The current
upstream `IsRegular` requires eventual boundary equality, whereas the old proof
selected cycle equality. The existing stationarity theorem supplies both.
This changes only a theorem proof; no signatures, definitions or public imports change.

## Old

```lean
  have hreg : X.IsRegular := by
    intro p q
    exact ⟨R p q, fun t ht ↦ hZ p q t ht⟩
```

## New

```lean
  have hreg : X.IsRegular := by
    intro p q
    exact ⟨R p q, fun t ht ↦ hB p q t ht⟩
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FiniteCoconeExactCouple | unclaimed when checked | Compiles unchanged with the repair; no signature or public-import change. |

The direct consumer is quarantined and was compiled in a scratch sandbox against
the restored module. Its weak-convergence theorem and the repaired theorem both
use only the three permitted axioms. Transitive consumers need no adaptations.
No target definition changes; no target statement review is reopened.

## Status

landed 20261023T102437-L-2899614 2026-10-23 (merge of deliver/C1/Sheaf.CategoryTheory.FiniteCoconeLimits)
