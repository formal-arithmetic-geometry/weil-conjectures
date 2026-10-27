## What changed

Proved `WeilConjectures.scalarModelRoosZeroLift_core` in
`Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore` without changing its statement or
any existing definition. Private helpers construct the levelwise scalar map from
the normalized ordinary scalar adjunction, prove its naturality and tensor
formula, and assemble the compatible first-coordinate family using
`CochainComplex.mappingCocone.lift` with zero shifted cochain. Proof imports expose
existing private normalization lemmas and the proved ordinary scalar adjunction.
The item's DAG proof and proof dependencies now describe this construction.
Scalar extension is applied to each coordinate before taking the product, so no
commutation of tensor products with countable products is required.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.scalarModelRoosZeroLift_core`
(node `lem-trf-scalar-model-roos-zero-lift-core`). No holes remain in the item.
No holes were added or split off. All new private helpers have complete proofs.
The complete module compiled through `lcompile.py` in 41.7 seconds. The existing
definition block and theorem signature were checked byte-for-byte against the
original. A theorem-local linter setting records that the original realization
parameters are intentionally unused by the strict construction.

## No longer needed

No original import, module, or node is withdrawn. The old proof plan's
simultaneous strict quotient presentation and K-injective tower resolution are
unnecessary: the hypothesis already supplies a strict map with zero shifted
coordinate, and ordinary scalar adjunction extends its compatible coordinates.
The original dependency on integral comparison realization models remains.

## Where the brief, the DAG or earlier work was wrong

The old node plan introduced resolutions that this strict construction does not
need. The replacement proves the original statement directly; its source and
unit route are preserved. No statement or definition repair was required.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore": "12aae67318fda74553f6655005b7dfa4a65dabc0"}, "results": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence": {"hash": "ad3dab305234dd1c065828ea0c45c7c89324a5f0", "status": "INFRA"}, "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization": {"hash": "0c8e7fbdbbe1945ef3a238f25b70457b3358a968", "status": "OK"}}, "seconds": 115, "time": "2026-10-28T05:41:08+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
