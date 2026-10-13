# AlgebraicGeometry.chow_relative_ample_twist_iso

## Reason

The isomorphism uses composition of tensor pullback and equality of the two morphisms to
integral projective space. Ampleness contributes no declaration or instance to this statement
or proof, so its unused public import is removed. No declaration, definition, signature,
visibility, or target meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Ample
```

## New

The import is removed. All other imports and the complete theorem signature are unchanged.

## Users

The only direct importer is the parent below. It publicly imports Ample itself, so removal
here does not change its available ampleness interface. All transitive importers retain
that independent route through the parent. The import pruning check passed. Attempting to compile the unchanged parent against the
sandbox overlay stopped because the existing module
`Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistProperties` has no compiled artifact in
the shared snapshot. This is unrelated to the removed import. No parent source was delivered
or adapted; independent reader/global build can recheck once that artifact is available.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwist | unclaimed | Unchanged: imports Ample directly; no adaptation needed. |

## Status

landed 20261013T000043-L-2230744 2026-10-13 (merge of deliver/A2/Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistIso)
