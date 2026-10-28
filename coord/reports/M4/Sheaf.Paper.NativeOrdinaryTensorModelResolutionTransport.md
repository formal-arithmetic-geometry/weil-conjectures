## What changed

Replaced the single hole in `Sheaf.Paper.NativeOrdinaryTensorModelResolutionTransport`
with a resolving-class construction. For a fixed native K-flat first input, the actual
ordinary tensor total followed by localization descends to the homotopy category.
The tensor-cone comparison proves that it inverts quasi-isomorphisms. The existing
`CategoryTheory.exists_natTrans_from_resolvingClass` extends the supplied comparison
on K-flat second inputs; naturality along a resolution proves its components are
isomorphisms. Its restriction equation and naturality give exactly the two required
conclusions.

All helpers are private and proved. The public theorem signature, public imports,
and existing definitions are unchanged. The node's proof, proof dependencies and
proof origin now describe the Lean argument. The existing common-roof theorem,
applied to an identity, supplies native K-flat resolutions; no new split is introduced.
The argument applies to unbounded complexes and includes zero complexes and zero maps.
The tensor implementations are marked locally irreducible while elaborating this file;
these attributes do not affect importers.

Validation: the final file compiled through `lcompile.py` without errors or warnings
in 58.2 seconds, within the 60-second limit. The public theorem signature and public
imports were checked unchanged, and the DAG dependency records match the proof.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_transport`
(node `lem-sf-native-weil-tensor-resolution-model-transport`).

There are zero `sorry`s left in the item and zero added holes. There are no new modules
or declarations with holes. The imported existing
`native_ordinary_tensor_model_resolution_roof` remains an independent assigned item;
its statement supplies resolutions and is used here as intended for stage 3.

## No longer needed

No original Lean import is removed and no module is withdrawn or pruned. The node no
longer cites `lem-pc-kflat-resolution` directly: native replacements are obtained from
`lem-sf-native-weil-tensor-resolution-roof`. That resolution node remains needed
indirectly by the roof theorem. The former independent-resolution-comparison step is
handled by the already proved resolving-class descent theorem, rather than a new hole.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing library already contains the general
resolving-class descent argument, so the original two-step plan does not require
another split. The sibling native roof theorem provides exactly the density input
without introducing an additional comparison between the native module tensor and
the separate sheaf-of-modules tensor construction. The unit route is unchanged.

Searches used LeanFinder, Loogle and Mathlib grep through `msearch.py`, together with
source searches of `lean/WeilConjectures` and `lean/Sheaf`. The usable existing result
is `CategoryTheory.exists_natTrans_from_resolvingClass`; the other searches returned
generic localization or homotopy results and no exact specialized transport theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionTransport": "1cf1e5a40894a41f13080581c77d03d3e48ca5f9"}, "results": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionData": {"hash": "1d8c0806bd1ed91d5fdc588b24dca8e5c96bbf83", "status": "OK"}}, "seconds": 89, "time": "2026-10-28T10:35:35+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
