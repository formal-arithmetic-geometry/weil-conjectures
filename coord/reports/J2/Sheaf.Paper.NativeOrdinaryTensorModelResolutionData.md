## What changed

Proved `native_ordinary_tensor_model_resolution_data` by combining two strictly
simpler resolution statements.  The transport component supplies the extended
model, its K-flat restriction equation, and its augmentation transport equation.
The roof component supplies the common K-flat roof for every map of second
complexes.  The target module imports these two new proof-only modules and
packages their outputs.  The target theorem signature and statement are
unchanged.

## Proved and sorry left

Closed the original sorry in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_data`.
The delivery adds exactly two split-off sorries:

- `native_ordinary_tensor_model_resolution_transport`, node
  `lem-sf-native-weil-tensor-resolution-model-transport`;
- `native_ordinary_tensor_model_resolution_roof`, node
  `lem-sf-native-weil-tensor-resolution-roof`.

Both split statements are strictly smaller components of the target and retain
the K-flat-resolution source argument in their docstrings.

## No longer needed

The target proof does not use the direct proof import
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; the two new
modules carry only the public interfaces needed by the split statements.  The
original direct dependency `lem-pc-kflat-resolution` is therefore no longer a
proof dependency of the target module itself; it remains the declared source
dependency of each split-off node for the future proofs.  No existing library
module or declaration was removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan bundled the model transport and common-roof
construction into one large theorem.  No existing declaration states that
specialized conjunction, so a complete direct proof was not available from the
published interfaces.  The route was decomposed into the two component nodes
above; the target's mathematical statement and unit route are unchanged.

## New nodes

`lem-sf-native-weil-tensor-resolution-model-transport` records the extension,
restriction, and augmentation transport component in
`dag/nodes/sec-six-functors/lem-sf-native-weil-tensor-resolution-model-transport.json`.

`lem-sf-native-weil-tensor-resolution-roof` records the common K-flat roof
component in
`dag/nodes/sec-six-functors/lem-sf-native-weil-tensor-resolution-roof.json`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionData": "1d8c0806bd1ed91d5fdc588b24dca8e5c96bbf83", "Sheaf.Paper.NativeOrdinaryTensorModelResolutionRoof": "505aff4689b95aa5b8db2bafb7448a352fa84ab4", "Sheaf.Paper.NativeOrdinaryTensorModelResolutionTransport": "5e1cd5ef90a69d648f97c2ea1906f5867de8c852"}, "results": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension": {"hash": "24138241f806d3427c32f3e2d624e5f1e1001468", "status": "INFRA"}, "Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality": {"hash": "3e71761aa21e0b2af670e66f3a4f73ba0b3dab60", "status": "OK"}}, "seconds": 123, "time": "2026-10-28T08:00:47+0800", "transitive": 0, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
