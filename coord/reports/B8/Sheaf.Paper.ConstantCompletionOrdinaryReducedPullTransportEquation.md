## What changed

Marked `CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq` as
`STATEMENT-DISPUTED`. The theorem quantifies over arbitrary isomorphisms `s` and `t`
with the same codomain and asserts a fixed equality involving both. No proof was added,
because this is false without normalization hypotheses on `s` and `t`.

## Proved and sorry left

No holes were closed. The existing sorry in
`CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq` remains, with its
existing DAG node. No new sorry was added.

## No longer needed

None. The imported source and target transport modules remain needed by the surrounding
transport construction.

## Where the brief, the DAG or earlier work was wrong

The statement is false as written. If a valid pair `(s,t)` satisfies the displayed
identity, postcompose `t` with any nontrivial natural automorphism of the common target.
The resulting `t'` has exactly the same stated type and remains an isomorphism, while
`Functor.whiskerRight (ordinaryPullComparison F A I) ... ≫ t'.hom` changes by that
automorphism and generally differs from `s.hom`. The source proof text refers to
“normalized transports”, but no normalization condition appears in the Lean binders.
The theorem needs hypotheses tying `s` and `t` to the quotient-unit normalization (or
must quantify over canonically constructed transports) before it can be proved.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation": "21720de89e0fdac6157776a9a48266594d01cf84"}, "results": {}, "time": "2026-10-28T07:54:08+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
