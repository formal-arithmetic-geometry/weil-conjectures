## What changed

Added `Sheaf.Paper.EtaleQuotientTensorProjectionProperFactor`, proving the first
proper/open factorization step of the assigned projection calculation by unfolding
the published compact scalar map. The assigned module imports and invokes this helper while retaining the original unresolved tensor-pasting step.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.compactScalarMap_proper_open_factor`, with no sorry.
The assigned theorem `AlgebraicGeometry.Etale.etaleQuotientTensorProjection` remains
with its original sorry; no new sorry was added.

## No longer needed

None. The helper is a standalone reduction step and does not alter the assigned
module's imports.

## Where the brief, the DAG or earlier work was wrong

The existing assigned theorem is a long proper/open tensor pasting identity. Its
first DAG step was not represented by a Lean declaration, so this delivery records
that definitional factorization as a separate proved node. The remaining tensor
pasting and constant-sheaf comparison steps are still open.

## New nodes

`lem-pur-etale-quotient-tensor-projection-proper-factor` records the proved
proper/open factorization and its source in Construction 2.26.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleQuotientTensorProjection": "f913b25ee190831f0992973a20aad4d68a02e0dd", "Sheaf.Paper.EtaleQuotientTensorProjectionProperFactor": "ef4aa70d08ee9f4348bd55bd1759bdd3370c53ae"}, "results": {}, "time": "2026-10-28T00:57:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
