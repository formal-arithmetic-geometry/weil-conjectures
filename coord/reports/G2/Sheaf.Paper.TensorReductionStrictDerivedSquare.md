## What changed

Proved `WeilConjectures.tensorReductionStrictMap_derived_square` in the item module.
Added `Sheaf.Paper.TensorReductionCanonicalSquare`, which packages the strictly
simpler existential canonical representative square and its finite-component
characterization. The item imports that helper privately for its proof.

## Proved and sorry left

The item theorem `tensorReductionStrictMap_derived_square` is proved, closing one
sorry. The new helper theorem
`WeilConjectures.tensorReductionCanonicalSquare_exists` remains as one named sorry,
with node `lem-coef-tensor-reduction-canonical-square`; its finite predicate is a
real definition with no sorry.

## No longer needed

No proof-dependency imports or DAG nodes were pruned. The proof uses the completed
pullback tower realizations, strict tensor assembly, and the new canonical-square
helper.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the explicit intermediate transport statement
needed to pass from the calculus normalization existential to the selected strict
chain map. This delivery records that transport as a separate, strictly simpler
node and then uses strict assembly uniqueness. No target statement was changed.

## New nodes

`lem-coef-tensor-reduction-canonical-square` records the existential canonical
representative square before strict-map selection. Its source is the transport of
the simultaneous reduction-tensor normalization in Stacks 07A4, 07A6 and 0941.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TensorReductionCanonicalSquare": "5f030e97c3e8e34ed87a0ffd9aad11080aacb68b", "Sheaf.Paper.TensorReductionStrictDerivedSquare": "a884df23f43c5290a5d22698f754e4858e84e441"}, "results": {}, "time": "2026-10-28T00:24:42+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
