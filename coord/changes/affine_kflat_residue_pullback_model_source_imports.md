# affine_kFlat_residuePullback_model source imports and additive instance

## Reason

The prior Sheaf copies of the derived-pullback and affine K-flat APIs were
withdrawn during the upstream sync. This repair uses their adopted
`WeilConjectures` declarations directly. The adopted source tree does not
register an additive instance for module scalar extension, while the existing
public theorem statement elaborates a derived-category complex containing
`ModuleCat.extendScalars`; the module therefore supplies the standard
left-adjoint additive instance needed to elaborate that unchanged statement.

## Old

The restored module imported the withdrawn Sheaf copies:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import Sheaf.Algebra.Homology.KFlatPullback
```

No `extensionScalars_additive` instance was declared in the module.

## New

The proof imports the adopted source modules and the K-flat API:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
```

The withdrawn empty `Sheaf.Algebra.Homology.KFlatPullback` import is removed.
The module adds the following public instance, which is the standard
left-adjoint additive instance and does not alter any theorem signature:

```lean
instance extensionScalars_additive {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) : (ModuleCat.extendScalars.{u, u, u} r).Additive := by
  exact (ModuleCat.extendRestrictScalarsAdj r).left_adjoint_additive
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel | M2 | Uses the adopted source APIs and instance while preserving the theorem signature. |
| Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison | unclaimed | Imports the theorem; its interface is unchanged. |
| TargetsCheck | maintainer | Reaches the item through the target closure; no interface change. |

## Status

landed 20261020T221243-L-4164376 2026-10-20 (merge of deliver/M2/Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel)
