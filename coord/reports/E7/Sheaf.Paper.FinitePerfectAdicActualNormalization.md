## What changed

Proved `finitePerfectAdic_actual_normalization` by constructing its required structure from two strictly smaller split obligations. Added `FinitePerfectAdicActualLevels` for levelwise descent and `FinitePerfectAdicActualRealization` for scalar realization and normalized transition identities. The top-level module imports both proof-only modules.

## Proved and sorry left

The original theorem is reduced to the two named intermediate theorems. The new declarations `finitePerfectAdic_actual_levels` and `finitePerfectAdic_actual_realization` remain `sorry`, with matching DAG nodes. No definition contains a `sorry`.

## No longer needed

The original broad proof dependency list is pruned to the two split obligations; the detailed lower-level dependencies are recorded on those nodes. No imported module from the original source was removed.

## Where the brief, the DAG or earlier work was wrong

The original node treated levelwise finite quotient descent and pro-etale scalar realization as one indivisible obligation. They are independent strictly smaller structures, and the parent combines them by field projection and a concrete structure literal.

## New nodes

`lem-weil-pbc-finite-perfect-adic-actual-levels` and `lem-weil-pbc-finite-perfect-adic-actual-realization` are added under `sec-proper-base-change`; their Lean declarations and proof obligations are in the corresponding new modules.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicActualLevels": "f9035b5d2ae45f2a1352cbbeb88d0475c5b23588", "Sheaf.Paper.FinitePerfectAdicActualNormalization": "1764b372fd4e4226ac50fdb90273a4393c752717", "Sheaf.Paper.FinitePerfectAdicActualRealization": "498795af7df7bce3831b0f38a546e9b1b5984ae8"}, "results": {}, "time": "2026-10-27T23:48:18+0800", "transitive": 0, "version": 1}
```

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
