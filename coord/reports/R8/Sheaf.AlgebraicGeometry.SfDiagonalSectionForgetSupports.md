## What changed

Restored the imported source module `Sheaf.AlgebraicGeometry.OrdinaryProperForgetComparison` required by the item and its unit reduction, and added the proof dependency module `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit`, stating the coefficient-free (tensor-unit and identity-map) diagonal normalization as a strictly simpler step. The assigned and unit modules now import the restored ordinary proper comparison source; the assigned module also imports the unit dependency; its original theorem remains available with its proof obligation recorded explicitly.

## Proved and sorry left

No existing hole was closed. Added one named split-off hole, `diagonalSection_forgetSupports_unit`, in `Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit` (node `lem-sf-diagonal-section-forget-supports-unit`). The assigned theorem `diagonalSection_forgetSupports` remains a sorry and now records the reduction to the coefficient-free normalization followed by naturality.

## No longer needed

None. The ordinary proper comparison is required by the displayed theorem and by the split-off unit theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG proof describes a full compactification-tower calculation, but the published library exposes no theorem equating that tower compositor with the ordinary compositor. The coefficient-free normalization is therefore split out as the first concrete categorical step so it can be proved independently, after which coefficient naturality handles the general map.

## New nodes

`def-sf-ordinary-proper-forget-comparison` records the restored source wrapper and change record `coord/changes/ordinary-proper-forget-comparison.md`. `lem-sf-diagonal-section-forget-supports-unit` records the tensor-unit and identity-map specialization, with its source and proof plan in the new module's docstring.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.OrdinaryProperForgetComparison": "b7ac14df5b56eb9dd70c2815746dcc622c4f055e", "Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports": "fc837f993ee310e783948ddde98e1ab428fadf51", "Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit": "b9918441cb7f86f410e753612990ad8d578f3f0a"}, "results": {}, "time": "2026-10-28T00:04:28+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
