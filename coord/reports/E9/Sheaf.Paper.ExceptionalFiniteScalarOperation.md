## What changed

Filled `finiteScalarOperation_exists` by packaging the existing finite exceptional operation
construction. Added `Sheaf.Paper.ExceptionalFiniteScalarOperationCore`, whose core package
contains the restricted functors, adjunction, and shift data; the final normalization equation
is isolated as a strictly smaller transport theorem. The item imports this core module.

## Proved and sorry left

The item theorem `finiteScalarOperation_exists` is proved. Two strictly smaller intermediate
statements remain as named sorries: `operationCore_exists` (construction of all operation data
except normalization) and `operationCore_normalized` (the single normalization transport
identity). They are recorded by the two new DAG nodes below.

## No longer needed

The proof does not need a direct import of `Sheaf.Paper.ExceptionalFiniteOperations`; its
existing theorem is used only as the declared proof dependency of the split core statements.
No existing DAG dependency was otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The one-step DAG plan omitted the substantial conversion from the ambient realization theorem
to the `Operation` record's fixed-coordinate normalization field. This delivery records that
conversion as a separate, strictly smaller statement so the upper packaging proof is complete.

## New nodes

`lem-sf-exceptional-finite-scalar-operation-core` records the core operation package.
`lem-sf-exceptional-finite-scalar-operation-normalization` records its single normalization
identity. Both node files are in `dag/nodes/sec-six-functors/` in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteScalarOperation": "a365ca7922e15d0e612f9438968f2551c2036e9b", "Sheaf.Paper.ExceptionalFiniteScalarOperationCore": "72fc954e7fc9c157c069516944a13a5278cfc3de"}, "results": {}, "time": "2026-10-28T03:56:02+0800", "transitive": 0, "version": 1}
```

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
