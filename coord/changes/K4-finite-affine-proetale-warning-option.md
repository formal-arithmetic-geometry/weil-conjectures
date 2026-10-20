# AlgebraicGeometry.finite_affine_proetale_refinement

## Reason

The returned delivery be70f32eb passed mathematical review, but landing rejected the
file-level warning option as an unattributed hole. Remove that unnecessary option.
The preflight conservatively treats a file-level option change as an interface change,
so this record documents it explicitly. The theorem's signature, visibility and all
public imports remain identical. Its proof has no holes.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

The explicit warning override is removed. Lean options set by this command apply to
subsequent commands in the same file and do not propagate to importing modules.
No mathematical statement or definition changes, and no target needs a statement review.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement
--uses finite_affine_proetale_refinement`, rerun for the repair of `30fc924054`, lists
zero downstream modules and finds no textual use of the theorem outside its defining
module. The former consumer `Sheaf.Paper.InternalHomDualConstructibleModels` no longer
imports this module. Neither consumer adaptation nor a change to a held module is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement | K4 | Remove the warning override; prove the unchanged theorem. |

## Status

landed 20261020T141312-L-2034573 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement)
