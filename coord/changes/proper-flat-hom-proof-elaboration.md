# proper_flat_rightAdjoint_affine_baseChange_hom_bijective proof elaboration

## Reason

The static interface checker treats module-level elaboration options as commands
changing visibility. These options only control elaboration of the new proof;
no existing declaration signature, visibility, definition or mathematical meaning changes.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | Proof elaboration only; every existing signature and visibility is identical. |

The options are local to this file's elaboration and do not alter imported declarations.
No consumer fails to compile and no forced adaptation is necessary. No target review reopens.

## Status

landed 20261013T072410-L-1126384 2026-10-13 (merge of deliver/V1/Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective)
