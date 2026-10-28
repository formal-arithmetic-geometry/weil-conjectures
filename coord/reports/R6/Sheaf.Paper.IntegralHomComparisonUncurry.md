## What changed

Added and compiled the elementary inverse-curry cancellation helper
`reduction_curry_symm_apply`, which records the categorical cancellation used by the
uncurrying argument. The assigned theorem remains open because the library has no
interface theorem relating an arbitrary `ReductionPresentation` to the independently
chosen model used by `integralHomReductionComparison`.

## Proved and sorry left

Proved: private helper `reduction_curry_symm_apply`.

Sorry left: `WeilConjectures.integralHomComparison_uncurry_eq` (node
`lem-sfb-integral-hom-comparison-uncurry`).

## No longer needed

None. No imports were removed and no DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan cites cochain tensor rigidity, but the current declarations do not
provide a bridge from that generic rigidity result to the concrete
`IntegralHom.ReductionPresentation` fields. After unfolding, the remaining goal is
exactly this missing bridge. The existing parent normalization theorem cannot be
imported because it imports this module, creating a cycle.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomComparisonUncurry": "a524abd36dbc908082958064acf49199caf34e6d"}, "results": {"Sheaf.Paper.IntegralHomComparisonNormalization": {"hash": "7cc9cf2a61105074fb8426658f82708eb150006a", "status": "OK"}}, "seconds": 54, "time": "2026-10-28T08:06:25+0800", "transitive": 0, "version": 1}
```

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
