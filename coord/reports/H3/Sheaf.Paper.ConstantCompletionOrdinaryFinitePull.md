## What changed

Filled the item theorem by reducing it to two strictly simpler public statements. Added
`ConstantCompletionOrdinaryFinitePullExistence` for construction and normalization, and
`ConstantCompletionOrdinaryFinitePullUniqueness` for the insertion-generator extensionality.
The item combines them into the required `∃!` proof. All three modules compile together.

## Proved and sorry left

`CategoryTheory.ConstantCompletion.ordinaryFinitePull_existsUnique` is proved from the two
split statements. The new declarations `ordinaryFinitePull_exists` and
`ordinaryFinitePull_unique` retain one `sorry` each for their independent downstream proofs.
No definition contains `sorry`.

## No longer needed

No imports from the original item were removed. The proof uses the existing derived-pull and
constant-completion declarations through the helper modules; no additional route dependencies
were needed.

## Where the brief, the DAG or earlier work was wrong

The original node presented a long construction and uniqueness argument as one hole. The
usable Lean interface is better represented by the existence/normalization and generator
uniqueness split, which are strictly simpler and compose by ordinary `∃!` reasoning.

## New nodes

`lem-weil-pbc-constant-completion-ordinary-finite-pull-existence` records the normalized
comparison construction. `lem-weil-pbc-constant-completion-ordinary-finite-pull-uniqueness`
records the generator extensionality argument. Both are in the item chapter and unit.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryFinitePull": "1511cf7191ee512b808f4ce277ad3a94901698a9", "Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence": "5e812fba4cfe7eda1ee856668fad9e7f29ecdbc6", "Sheaf.Paper.ConstantCompletionOrdinaryFinitePullUniqueness": "37afb385c26fc9d9cef069c7f0a9605d50e04030"}, "results": {}, "time": "2026-10-28T00:00:14+0800", "transitive": 0, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
