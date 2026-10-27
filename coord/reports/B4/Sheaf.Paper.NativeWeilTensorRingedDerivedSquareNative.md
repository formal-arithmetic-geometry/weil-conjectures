## What changed

The assigned module now assembles its native derived-square conclusion from the
proved representative-square comparison and a new, strictly simpler coherence
component.  Its theorem signature and target statement are unchanged.  The
representative-square theorem and its private localization helpers were moved to
`Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeComparison`; this keeps each
slow declaration in a separate module and leaves the comparison theorem's public
statement unchanged.  The target module imports the comparison and coherence
modules privately and no longer imports the comparison-only naturality and
bifunctor helper modules directly.

The new module
`Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence` states the remaining
`Nonempty (RingedForgetTensorTransposition.TensorCoherence ...)` component with the
full representative-square equation as an input.  Its proof is intentionally the
whole named split-off obligation and is recorded by node
`lem-sf-native-weil-tensor-ringed-derived-square-native-coherence`.

## Proved and sorry left

The original hole
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_data`
is closed by a genuine decomposition: the complete Lean proof constructs `t` and
its representative square with
`native_weil_tensor_ringed_derived_square_comparison`, then applies the named
coherence component.  This is one upper hole decomposed into one strictly simpler
lower hole, rather than a direct proof of coherence.

The comparison declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison`
has no `sorry` and remains fully proved.  The only `sorry` delivered is the whole
proof of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_coherence`
in the new module, attached to node
`lem-sf-native-weil-tensor-ringed-derived-square-native-coherence`.

Holes closed: 1 by decomposition.  Holes added: 1.  Sorries remaining in the
assigned module: 0; in the delivery: 1 named split-off theorem.  No definition
contains a `sorry`.

## No longer needed

The assigned module no longer needs direct proof imports
`Sheaf.Paper.NativeWeilTensorRingedModelNaturality` and
`WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`; those imports and
`Mathlib.CategoryTheory.Localization.Prod` remain in the comparison sibling where
the private localization proof uses them.  The previously removed ordinary-data
and fresh-resolution route remains unnecessary for the representative-square
component.  No unit statement or unit proof step is bypassed, and no existing
mathematical node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The inherited proof plan's second step treats transport of `d.coherence` as if it
immediately gave coherence for the comparison normalized by the arbitrary supplied
ordinary model.  The existing normalization and naturality clauses do not state
that compatibility.  The concrete missing transport is therefore isolated as a
strictly simpler theorem instead of being silently asserted in the parent proof.
The prior representative-square route was valid and is preserved; only its module
placement changed to meet the per-file compile limit.

## New nodes

`lem-sf-native-weil-tensor-ringed-derived-square-native-coherence` records the
remaining coherence transport component.  Its module is
`lean/Sheaf/Paper/NativeWeilTensorRingedDerivedSquareNativeCoherence.lean`.

The existing node
`lem-sf-native-weil-tensor-ringed-derived-square-comparison` now records its
unchanged declaration in
`lean/Sheaf/Paper/NativeWeilTensorRingedDerivedSquareNativeComparison.lean`.
The placement change is recorded in
`coord/changes/native-weil-tensor-ringed-derived-square-comparison-module.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": "977bd4142d368d9611d807dca1f0bd01755b6156", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeCoherence": "9bfcf31d46bcbc7d5ec96ae4dc65abc96ff01cba", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeComparison": "9d41d5591d7e4dc04c38f1fd3dfc2091feac4ffc"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquare": {"hash": "5b025cfd7e4859282042e936f945814922d493b6", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T05:28:38+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
