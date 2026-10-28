## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_naturality`
in `Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality`, preserving its entire statement.
The proof takes the roof supplied by `hresolution`, applies homotopy invariance before and after
ordinary total tensor, uses `htransport` and `hkflat`, and cancels the image of the resolution
quasi-isomorphism. A proved private helper `ordinaryTensorMap_comp` supplies functoriality of
ordinary total-tensor maps using the coproduct inclusions and bifunctor naturality.
A second proved private helper, `naturality_of_transport`, performs the categorical
cancellation with abstract morphisms, avoiding repeated unfolding of complex-map instances.

Replaced the unused proof import of `Sheaf.Paper.NativeOrdinaryTensorModelResolutionData`
with `Mathlib.Algebra.Homology.BifunctorHomotopy`. Updated the item's node proof and
proof dependencies to match this direct argument. No public interface or definition changes. A declaration-scoped unused-variable linter
option retains the existing binder names, including names nested in the hypotheses.

Searches through the supplied msearch wrapper used LeanFinder, Loogle, and Mathlib grep.
They found `DerivedCategory.Q_map_eq_of_homotopy` and
`HomologicalComplex.mapBifunctorMapHomotopy₂`, which are used directly.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_resolution_naturality`
(node `lem-sf-native-weil-tensor-resolution-model-naturality`).

No `sorry` remains in the item, no holes were added, and no statements were split off.
The private helpers `ordinaryTensorMap_comp` and `naturality_of_transport` are fully proved.

The complete proof compiled through `lcompile.py` in 27.6 seconds, below the 60-second limit.
The theorem statement was also compared verbatim with the original source.

## No longer needed

Removed this item's proof import of
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionData` and its proof-dependency edge to
`lem-sf-native-weil-tensor-resolution-model-data`: all resolution and transport data needed here
are explicit hypotheses. The data theorem remains needed by
`Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension`, which imports it directly and
constructs the hypotheses passed to this theorem. No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned use of `lem-sf-native-weil-tensor-resolution-model-data` is unnecessary inside
this theorem: its data are already assumed. The common-roof proof plan itself is correct and
is implemented without any new mathematical assumptions or intermediate obligations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionNaturality": "928b39b27b73923d9285702475ae7e505f617cf2"}, "results": {"Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension": {"hash": "24138241f806d3427c32f3e2d624e5f1e1001468", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T08:00:35+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
