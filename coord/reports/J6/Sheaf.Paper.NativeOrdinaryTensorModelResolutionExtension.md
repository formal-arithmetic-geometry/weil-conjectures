## What changed

Closed the assigned theorem by a real Lean reduction.  The item now imports two
strict lower statements: resolution transport data and the naturality consequence
of that data.  Its proof obtains the transported model, rewrites the normalization
using equality on K-flat second inputs, and applies the naturality consequence.

The two lower statements are in
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionData` and
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality`.  Their proofs remain
named `sorry` statements because the current library has the K-flat resolution
existence theorem but no canonical comparison or common-roof API for this native
model.  The assigned module's target signature is unchanged.

## Proved and sorry left

The assigned hole is closed:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_extension`
  (node `lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`).

Two strict lower holes are added, one in each new module:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_data`
  (node `lem-sf-native-weil-tensor-resolution-model-data`), which supplies the
  transported model, its K-flat restriction equation, the resolution transport
  identity, and common K-flat roofs;
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_naturality`
  (node `lem-sf-native-weil-tensor-resolution-model-naturality`), which derives
  arbitrary second-variable naturality from those transport equations and roofs.

Thus one of one original sorries is proved, two are split off, and two sorries
remain in the target import closure.  No sorry occurs in a definition.

## No longer needed

Removed the item's direct proof import
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; the item proof
uses only the two new declarations.  That module remains imported by the
resolution-data module, where `lem-pc-kflat-resolution` is still a proof dependency.
The original direct dependency `lem-pc-kflat-resolution` is therefore relocated
below the two new nodes rather than pruned from the target route.  No other module
or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's direct proof plan treats the K-flat resolution existence theorem as if it
also supplied canonical localized tensor comparisons and common K-flat roofs.  The
live declaration supplies only a K-flat complex, an augmentation, quasi-isomorphism,
and degreewise epimorphisms.  The missing comparison and roof coherence are genuine
strict subarguments, so they are recorded as the two new nodes instead of being
hidden in a partial proof.  The route still follows the unit's resolution-extension
step and keeps the supplied K-flat naturality hypothesis.

## New nodes

`lem-sf-native-weil-tensor-resolution-model-data` is stated in
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionData` and records the model,
restriction, transport, and common-roof data needed by the extension.  Its source
is Stacks Tags 06YS and 06YU as cited in the item blueprint.

`lem-sf-native-weil-tensor-resolution-model-naturality` is stated in
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality` and records the
common-roof cancellation argument that yields arbitrary second-variable
naturality.  Its source is Stacks Tags 06YU and 0FPT as cited in the item blueprint.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionData": "4b25c33c6a9bfbbbea363f09537c83878c835bbe", "Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension": "24138241f806d3427c32f3e2d624e5f1e1001468", "Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality": "3e71761aa21e0b2af670e66f3a4f73ba0b3dab60"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary": {"hash": "ff7c1fed7a1304082dcf2503aa6bca2861d25814", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T05:30:06+0800", "transitive": 0, "version": 1}
```

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
