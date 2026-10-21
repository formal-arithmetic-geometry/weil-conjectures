# AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction_comp

## Reason

The proof uses the same transparency settings as the existing constant-ring and
ring-sheaf comparison modules to identify the two existing notations for exact
scalar restriction and their derived functors. These elaboration options affect
only this file. All public signatures and the compact-support comparison definition
are unchanged. New helpers are private and fully proved; proof imports use `import all`
to reuse existing proved private generic calculations.

## Old

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
```

## New

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

`tools/downstream.py ... --uses
AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction_comp` lists only the item
itself as a textual user; no downstream module mentions the theorem yet. There are
84 transitive importers, but the public imports, statements, instances and data are
unchanged, so no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | Y2 | Proved theorem; private helpers and elaboration options. |

## Status

landed 20261021T151213-L-1180328 2026-10-21 (merge of deliver/Y2/Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction)
