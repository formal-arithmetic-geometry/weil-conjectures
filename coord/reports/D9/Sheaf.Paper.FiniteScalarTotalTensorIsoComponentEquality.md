## What changed

Proved `WeilConjectures.finiteScalarTotalTensorIso_representative_component_eq` by unfolding
`finiteScalarTotalTensorIso` and reducing the resulting object notation. The `FiniteScalarTensorComplex` dependency is private because `FiniteScalarTensorResolution`
already publicly imports it; the theorem's public declarations are unchanged. Added local
elaboration options and a local irreducibility hint for `finiteScalarFlatRepresentatives` to
keep elaboration within the file limit. The import and elaboration adjustment is recorded in
`coord/changes/FiniteScalarTotalTensorIsoComponentEquality.md`.

## Proved and sorry left

Closed the only sorry, `finiteScalarTotalTensorIso_representative_component_eq`. No sorries
were added.

## No longer needed

The proof does not use the realization theorem `lem-sf-finite-scalar-tensor-realization`
from the original proof plan. The node proof dependencies were pruned to
`lem-sf-finite-scalar-tensor-complex`; the resolution module remains needed for the
statement's representative predicate and is still imported publicly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan listed the realization node, but the stated equality is already a
component-level definitional reduction of the specialized total tensor isomorphism and
requires no realization argument.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarTotalTensorIsoComponentEquality": "752dac35ce65fb46d746175e239db172cc39091b"}, "results": {}, "time": "2026-10-28T00:48:17+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
