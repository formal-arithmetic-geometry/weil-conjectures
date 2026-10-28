## What changed

Replaced the hole in `sixFunctorProjectionFinite_left_route_expansion` by pasting two equations at an explicit intermediate comparison. The new `sixFunctorProjectionFinite_left_prefix` split theorem handles the pullback of the projection and the entire exchange map. It uses naturality of the pull realization, equivalence-unit cancellation, the existing proved fixed-component calculation, and naturality of the fixed exchange. Its proof imports `FiniteProjectionIterationRealization` privately to reuse the proved cancellation helpers.

The remaining equation, `sixFunctorProjectionFinite_left_tensor_transport`, concerns only support applied to tensor monoidality and the pullback-square comparison. It contains neither a projection component nor an exchange map. The original theorem's signature and every existing definition are unchanged. Both new modules publicly import only the coordinates needed to state their equations; the item's new imports are proof imports.

## Proved and sorry left

The original hole in `WeilConjectures.sixFunctorProjectionFinite_left_route_expansion` is closed by a complete pasting proof from the two named intermediate equations. Two holes are added: `WeilConjectures.sixFunctorProjectionFinite_left_prefix`, node `lem-sf-finite-base-change-left-prefix`, and `WeilConjectures.sixFunctorProjectionFinite_left_tensor_transport`, node `lem-sf-finite-base-change-left-tensor-transport`. The original module has zero holes; the delivery has two named strict sub-holes. This is a decomposition: one upper hole is closed and the two remaining equations separately isolate projection/exchange and final tensor normalization.

## No longer needed

No existing imports, modules or DAG dependencies are pruned. The original comparison, projection-mate and operation-stage definitions remain necessary through the two new equations. No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The original node grouped projection naturality, exchange naturality and pullback-compositor normalization into one step. The delivery proves the projection and exchange subcalculation and separates only the final tensor/compositor normalization. Its intermediate comparison is explicitly constructed from existing realization isomorphisms; no witness is chosen from an existence theorem. The prefix has no pullback-compositor assumption beyond the original datum, and the remaining statement has no projection or exchange. Thus the new hole is a strict part of the original argument rather than a renamed endpoint equation.

The later `ProjectionFormulaCoherence` module cannot serve as a dependency because it already depends on this item. The existing iteration-realization module supplies usable proved cancellation helpers without creating that cycle.

## New nodes

`lem-sf-finite-base-change-left-prefix` records the proved projection/exchange prefix in `lean/Sheaf/Paper/ProjectionFiniteBaseChangeLeftPrefix.lean`.

`lem-sf-finite-base-change-left-tensor-transport` records the remaining tensor and pullback-square normalization in `lean/Sheaf/Paper/ProjectionFiniteBaseChangeLeftTensorTransport.lean`. Its docstring and node give the argument via support naturality, cancellation of tensor comparisons, and `finitePullCompositionNormalization`. Zero inputs, identity maps and empty schemes use the same isomorphism identities; the first tensor input is not assumed to have finite Tor amplitude.

The addition record is `coord/changes/D6-left-route-prefix-and-tensor-transport.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeLeftPrefix": "47fe3e34e3c45292b1d960c73d512b1745e8cc3c", "Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion": "6845b366fc02f5ad4fedcfb6a54f77049542e9da", "Sheaf.Paper.ProjectionFiniteBaseChangeLeftTensorTransport": "bfecb1a2ebf97e0f9c042b457918492714e8aa3f"}, "results": {"Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation": {"hash": "d4cc4897b248d9875047df4666dcd051e142c41b", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T10:42:14+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
