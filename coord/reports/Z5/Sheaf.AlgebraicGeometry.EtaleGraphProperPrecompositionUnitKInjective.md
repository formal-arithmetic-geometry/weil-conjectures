## What changed

Added the proof module's representative-complex reduction. The original theorem is proved by
surjectivity of the homotopy-category quotient on objects, reducing it to the new
`graph_proper_precomposition_unit_component_on_complex` theorem in the companion core module.
The core theorem records the remaining K-injective geometric calculation as a named intermediate
statement for a later worker.

## Proved and sorry left

Proved `graph_proper_precomposition_unit_component` from the quotient-object surjectivity lemma.
One sorry remains in `graph_proper_precomposition_unit_component_on_complex`, the strict
representative-complex geometric calculation.

## No longer needed

None. The imports and declared dependencies remain needed by the representative calculation.

## Where the brief, the DAG or earlier work was wrong

The brief's single objectwise calculation is not directly reducible from the currently published
APIs. The quotient-object reduction is valid and exposes a strictly simpler intermediate theorem;
the unresolved geometric equality is isolated there.

## New nodes

`lem-pur-graph-proper-precomposition-unit-component-core` records the representative-complex
intermediate theorem and its remaining proof obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjective": "d9d042bc40bda60f3e13f6a44e3081bb5e54c1f1", "Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnitKInjectiveCore": "49aaebe5c5209736e12703b40a3ab41c3e14cfc4"}, "results": {}, "time": "2026-10-28T00:19:06+0800", "transitive": 0, "version": 1}
```

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
