## What changed

Retained the original endpoint-data structure and theorem signature. Expanded the
`STATEMENT-DISPUTED` declaration comment with the explicit countervariation that
composes the target endpoint isomorphism with an arbitrary automorphism. The theorem
remains `sorry` because its hypotheses permit this variation.

## Proved and sorry left

No theorem was proved. The sole sorry,
`WeilConjectures.integralOrdinaryProjection_endpointCompatibility`, remains and is
marked `STATEMENT-DISPUTED`. The endpoint data contains independent source and target
isomorphisms; replacing `d.t` by `d.t ≪≫ α` for a nontrivial target automorphism
preserves the data but changes the displayed square in general. No new sorry was
added.

## No longer needed

None. The existing imports and declared proof dependencies remain needed by the
endpoint-data type and its downstream users.

## Where the brief, the DAG or earlier work was wrong

The node asks for the square equation for arbitrary
`IntegralOrdinaryProjectionEndpointData`, but that structure records only two
independent isomorphisms and asserts no square compatibility. The equation therefore
is false for the stated data. Adding a compatibility field to
`IntegralOrdinaryProjectionEndpointData` would change the V1-owned endpoint-data
construction and its many consumers, so this delivery preserves that interface and
records the counterexample as required by the stage-3 disputed-statement process.
The endpoint-data owner or maintainer must correct the statement and its DAG
`statement_change` before this hole can be proved.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility": "6ff52730e8594efa3d26bd871843aaca512b0789"}, "results": {}, "time": "2026-10-28T07:49:36+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
