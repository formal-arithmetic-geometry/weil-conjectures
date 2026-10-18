# Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp public imports

## Reason

The proof constructs a concrete finite-presentation approximation using
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, whose `isLimit`
field already proves the required universal property. No statement or proof in the
assigned module uses a declaration from `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
Remove its unused public import as required by stage-3 pruning.
All existing declaration signatures, visibility and mathematical meanings stay identical.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

The import is removed. The remaining imports and the existing theorem signature are unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp
--uses exists_limit_affine_transition` lists these nine transitive consumers and finds
zero textual uses of the removed module's limit-existence declaration. The sole direct
importer is `FiniteClosedFpApproximation`, which already has its own explicit
`public import Sheaf.AlgebraicGeometry.LimitAffineTransition`, so its public import closure
continues to include that module. No consumer adaptation is necessary; no other group's
module is edited. The independent reader can check the direct importer's original file.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.FiniteClosedFpApproximation` | not adapted | Direct importer; already publicly imports `LimitAffineTransition`; no change. |
| `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |
| `Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible` | not adapted | Transitive consumer through `FiniteClosedFpApproximation`; no change. |

## Status

landed 20261018T062857-L-671535 2026-10-18 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp)
