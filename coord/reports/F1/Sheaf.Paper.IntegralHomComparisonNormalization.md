## What changed

Filled `WeilConjectures.integralHomComparison_normalization`. The proof applies
injectivity of the target adjunction's inverse Hom equivalence and unfolds
`IntegralHom.comparison`. Added `Sheaf.Paper.IntegralHomComparisonUncurry`, which
states the strictly smaller representative-level uncurried normalization needed by
that proof. The original rigidity import was removed because the item proof uses it
through the split theorem's proof dependency rather than directly.

## Proved and sorry left

The item's `integralHomComparison_normalization` sorry is closed. One strictly
smaller split statement remains sorry:
`WeilConjectures.integralHomComparison_uncurry_eq` in node
`lem-sfb-integral-hom-comparison-uncurry`.

## No longer needed

Removed the direct import `Sheaf.Algebra.Homology.CochainTensorModelRigidity` from
the item; the item only uses the uncurried normalization declaration. No other
nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the categorical injectivity step needed to compare
an arbitrary `ReductionPresentation` with the canonical chosen presentation. The
split theorem makes the missing representative normalization explicit; its statement
is strictly weaker than the item's equality of comparison morphisms.

## New nodes

Added `lem-sfb-integral-hom-comparison-uncurry`, stated in
`Sheaf.Paper.IntegralHomComparisonUncurry`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomComparisonNormalization": "7cc9cf2a61105074fb8426658f82708eb150006a", "Sheaf.Paper.IntegralHomComparisonUncurry": "8e33353dd45d2f85df8b8619b9172819b937e1e4"}, "results": {"Sheaf.Paper.IntegralConstructibleInternalHom": {"hash": "ba6b4739f9f2f4a250e47027785ee93459b155c7", "status": "OK"}, "Sheaf.Paper.IntegralGeneralLfpHomFiniteness": {"hash": "53c96b9861c9740ce3c69ba29c1984535d1ce409", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T06:45:45+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
