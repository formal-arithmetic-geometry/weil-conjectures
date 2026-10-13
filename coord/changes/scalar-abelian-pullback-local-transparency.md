# AlgebraicGeometry.Scheme.scalar_abelian_pullback_square

## Reason

The original statement and all existing signatures are unchanged. The proof uses a canonical inverse-image comparison and the proved coefficient adjunct. Repeated unfolding of the explicit integer-unit class and scalar inverse-image construction caused single-file compiles to exceed 60 seconds. A local irreducibility attribute keeps those definitions folded during this file's elaboration. The final original module compiles in 31 seconds. This record is required by the conservative command-change preflight check; the attribute is local and exports no change to other modules.

## Old

The existing module has no local irreducibility attribute on these two definitions:

```lean
attribute [local instance] Sheaf.monoidalCategory
```

The definitions of `scalarAbelianUnitClass` and `scalarInverseImage` are unchanged.

## New

```lean
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] scalarAbelianUnitClass scalarInverseImage
```

Both attributes are scoped to `ScalarAbelianPullbackSquare.lean`. No public or imported definition body, theorem type, instance signature, or visibility changes. The new modules are recorded by their own DAG nodes. This is an elaboration change in the held module, not an adaptation of another module.

## Users

The uses of the original theorem were inspected with `tools/downstream.py` and `rg`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare | S4 | Its proof elaborates with the two definitions folded; statement unchanged. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality | unclaimed | Calls the unchanged theorem; local attributes do not propagate to this importer. No adaptation. |

No target meaning changes and no forced adaptation is required.

## Status

landed 20261013T130752-L-3986965 2026-10-13 (merge of deliver/S4/Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare)
