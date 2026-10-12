# AlgebraicGeometry.limit_fibre_products_of_affine_transition (imports)

## Reason

The unchanged theorem signature needs only Mathlib.AlgebraicGeometry.Fiber.
LimitResidueField is needed only by the proof and must be a plain import.
The direct universal-property argument removes the need for FibreProductLimit.
LimitAffineTransition is not used directly: all three limiting cones are supplied
as hypotheses. It remains transitively available through LimitResidueField.
No declaration signature or definition changes, and no target meaning changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.AlgebraicGeometry.LimitResidueField
public import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.AffineFibreProductTransition
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.LimitResidueField
import Sheaf.AlgebraicGeometry.AffineFibreProductTransition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | P3 | Sole direct importer; imports LimitFibreProducts privately, also imports LimitResidueField and ProperLimitNoetherian directly. Its signature and original proof compile unchanged against the new module. |

The read-only downstream search found 211 transitive importers and no downstream
textual use of the removed modules' declarations
`exists_limit_affine_transition`, `exists_isColimit_residueField_of_isLimit`, or
`isIso_limit_pullback_comparison`. The direct importer does not publicly re-export
LimitFibreProducts, so the removed public imports are not propagated through it.
No forced adaptations are required.

## Status

landed 20261012T150957-L-2232215 2026-10-12 (merge of deliver/S1/Sheaf.AlgebraicGeometry.LimitFibreProducts)
