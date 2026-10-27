## What changed

The item theorem now obtains the normalized mixed scalar/open square and applies a
separate signed-symmetry postcomposition theorem.  It then cancels the final symmetry
isomorphism with a real `cancel_mono` step.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.etaleOrderedOpenProjectionScalar`.  One sorry remains
in `AlgebraicGeometry.Etale.etaleOrderedOpenProjectionScalar_postcomp`, split into node
`lem-pur-etale-ordered-open-projection-scalar-postcomp`.

## No longer needed

No imports or existing DAG dependencies were pruned; the mixed scalar/open theorem,
normalized coefficient comparisons, and signed tensor symmetry are used.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines a mixed scalar/open equation with a separate
signed-symmetry conjugation.  The latter is a strictly simpler postcomposed equality;
the item theorem now combines it with the mixed equation and cancels the isomorphism.

## New nodes

`lem-pur-etale-ordered-open-projection-scalar-postcomp` records the postcomposed
signed-symmetry and normalization step still required to prove the item theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleOrderedOpenProjectionScalar": "1506813f41e70a80da74740756d44ad2f0b9445a", "Sheaf.Paper.EtaleOrderedOpenProjectionScalarConjugation": "13a53f3379f5c0ffd5561b8000133b9a25822d7d"}, "results": {}, "time": "2026-10-28T03:50:41+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
