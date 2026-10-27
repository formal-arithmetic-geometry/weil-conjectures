## What changed

Added the mate-form intermediate theorem
`WeilConjectures.IntegralFiniteExtension.finiteU_quotient_transition_mate` and
proved the original `finiteU_quotient_transition` by injectivity of the level-m
scalar-adjunction hom equivalence. The existing imports are sufficient.

## Proved and sorry left

Proved `finiteU_quotient_transition` (one existing sorry closed). The new
intermediate theorem `finiteU_quotient_transition_mate` remains as one named
sorry, with node `lem-sf-finite-dualizing-mixed-quotient-mate`; it is the
transposed coefficient-counit square required by the proof plan. No definition
contains a sorry.

## No longer needed

None. The two existing imports remain used by the theorem and its mate form.
No existing DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omits a separately named Lean statement for its
central transposed mate calculation. The new node records that missing proof
step explicitly; the target theorem now combines it with a real injectivity
argument.

## New nodes

`lem-sf-finite-dualizing-mixed-quotient-mate` records the transposed
hom-equivalence equality and its source proof step.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": "8ae92ef154d75410c70494455498f5a090e07d50"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence": {"hash": "33e6258868e735e99734a98c2ddda6fb4b2830e1", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T06:52:14+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
