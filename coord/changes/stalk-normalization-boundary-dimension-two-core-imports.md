# stalk_normalization_boundary_dimension_two_target

## Reason

Prune two unrelated public imports from the local dimension estimate. Its statement
needs the dimension definition but no finite-etale cover or normalization.
The theorem's complete signature is unchanged. No definition or target changes.
This records the change to re-exported imports required by preflight (stage 3 §3.3).

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
```

## New

```lean
public import Mathlib.RingTheory.KrullDimension.Basic
```

Proof dependencies are non-public imports:

```lean
import Sheaf.RingTheory.FlatLocalDepthFormula
import Sheaf.RingTheory.DepthLeSupportDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
```

## Users

`tools/downstream.py --uses stalk_normalization_boundary_dimension_two_target`
finds only the assigned module itself and StalkNormalizationBoundaryDimensionTwo.
The direct-import scan also finds StalkNormalizationBoundaryDimensionTwoTransfer.
Both external direct importers already explicitly import the two removed modules;
therefore they continue to expose their declarations themselves. No adaptation is
necessary. The static import-pruning check passes. None of the 122 transitive
importers loses these modules through this route, since both immediate importers
retain them independently. No target's mathematical meaning is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore | J3 | Proof closed; unrelated re-exports removed; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo | unclaimed in the local claim snapshot | Uses the same theorem signature; explicitly imports both removed modules. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoTransfer | J3 | Explicitly imports both removed modules; no proof or signature change. |

## Status

landed 20261013T151701-L-924132 2026-10-13 (merge of deliver/J3/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore)
