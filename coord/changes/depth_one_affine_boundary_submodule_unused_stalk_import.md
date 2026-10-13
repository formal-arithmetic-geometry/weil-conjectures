# depth_one_affine_boundary_submodule: unused stalk import

## Reason

Remove the unused public `Mathlib.Algebra.Category.ModuleCat.Stalk` import from
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineBoundarySubmoduleDepth`.
Its theorem speaks about a module localized at a prime, not a sheaf stalk, and uses no
stalk declaration. No declaration signature, definition, visibility or docstring changes.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Stalk
```

## New

The unused import is removed. All existing declaration signatures and definitions are
unchanged. The two new helper modules are imported privately for the proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth | unclaimed (no adaptation) | Unchanged: its own public import of Mathlib.Algebra.Category.ModuleCat.Stalk preserves the stalk API for it and its importers; the boundary theorem signature is unchanged. |

This is the only direct importer. Every further importer reaches the boundary theorem
through this module, whose own public stalk import remains. Therefore no downstream
adaptation is required and no target's meaning changes.

## Status

landed 20261013T123549-L-3712479 2026-10-13 (merge of deliver/T4/Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineBoundarySubmoduleDepth)
