# AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientPullbackIso_square

## Reason

Restore the quarantined module identified in coord/rework.tsv. The upstream sync removed
`AlgebraicGeometry.Etale.pullbackSquareComparison_def`. The defining expression of
`Etale.pullbackSquareComparison` still gives exactly the required composite, so its private
normalization proof can unfold that definition directly. This is a proof repair of a
zero-hole module, with no change to its mathematical statement or constructions.

## Old

The archived private `etale_square_eq` proof began with:

```lean
  rw [Etale.pullbackSquareComparison_def]
```

The module is currently absent from lean/ and preserved in
quarantine/Sheaf/Paper/FiniteDiscreteCoefficientSquareCoherence.lean.

## New

The restored private proof begins with:

```lean
  unfold Etale.pullbackSquareComparison
```

Every declaration signature, public import, definition body and remaining proof line is
identical to the archived module. The existing DAG attachment, statement, proof route and
dependencies are retained; its proof-origin note records the restoration.

## Users

`tools/downstream.py` reports an unknown module because the item is quarantined. Searching
both lean/Sheaf/ and quarantine/Sheaf/ finds one direct importer and theorem consumer:
FiniteDiscreteCoefficientCoherentPullbacks. The other dependents below are recorded in
coord/rework.tsv. No consumer requires an adaptation because the restored interface is
identical to its archived interface. The restored module compiled in 24.9 seconds;
the unchanged archived direct consumer compiled against it in 4.6 seconds. Holder
labels reflect the local claim snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B6 | Restore the complete module; repair one private proof. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Direct archived consumer; unchanged. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Restore dependency; no interface change. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Restore dependency; no interface change. |

## Status

landed 20261021T140759-L-2746141 2026-10-21 (merge of deliver/B6/Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence)
