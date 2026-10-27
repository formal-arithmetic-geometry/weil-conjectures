## What changed

Imported `Sheaf.Paper.AdicReindexingTensorCompatibility` and added the new
`Sheaf.Paper.AdicReindexingUnitContraction` module. The item theorem now specializes
tensor compatibility at the coefficient unit and invokes the unit-contraction lemma.

## Proved and sorry left

The original theorem `normalized_reindexing_unit_compatibility` is closed. One new
strictly smaller intermediate theorem remains sorry:
`reindexing_tensor_unit_contraction` in
`Sheaf.Paper.AdicReindexingUnitContraction` (node
`lem-sf-adic-reindexing-unit-contraction`).

## No longer needed

No proof-dependency imports were removed. The proof uses the tensor compatibility
module and the new unit-contraction node; the other planned finite-completion and
cochain nodes are not imported by this item.

## Where the brief, the DAG or earlier work was wrong

The unit proof requires an explicit contraction step from the tensor square at the
coefficient unit to the chosen canonical unit witness. That step was absent as a
Lean declaration, so it was split into the new intermediate node.

## New nodes

`lem-sf-adic-reindexing-unit-contraction` is the degree-zero unit contraction of the
specialized tensor square. Its Lean declaration is in
`lean/Sheaf/Paper/AdicReindexingUnitContraction.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingUnitCompatibility": "163bcae68c8ec6e3b31e024fe6687d7e9dcbda16", "Sheaf.Paper.AdicReindexingUnitContraction": "4e52de3b176a0cecc6a545036a4e963c7bf55962"}, "results": {}, "time": "2026-10-28T05:37:52+0800", "transitive": 0, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
