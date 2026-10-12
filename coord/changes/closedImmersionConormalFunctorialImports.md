# ClosedImmersionConormalFunctorial imports

## Reason

The completed proof uses kernel lifts and the composite adjunction. The affine conormal
calculation and affine pullback-sections calculation are unnecessary. Prune these imports
and replace the public affine-sections import with the two actual statement dependencies.
The theorem signature, universes, hypotheses, visibility, and conclusion stay identical.
No definition changes, and no target interpretation changes or needs reopening.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AffineConormalSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullback

open CategoryTheory Opposite TopologicalSpace
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.EffectiveCartier

open CategoryTheory Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The transparency options match those used by the existing tensor-pullback modules and are
needed to elaborate their sheaf/module interfaces in this proof. `Limits` opens the namespace
containing `kernel.lift`. Neither change introduces a declaration or affects a signature.

## Users

The current import graph has three direct importers, listed below together with the item.
Independent review compiled all three unchanged against the delivered module; each passed
without errors or warnings and requires no adaptation. The maintainer performs the global build
after landing.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial | C1 | Same signature, completed proof; public imports reduced to actual statement dependencies. |
| Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange | unclaimed in local claims | Unchanged source compiles against the revised module; canonical-map hypothesis unchanged. |
| Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange | unclaimed in local claims | Unchanged source compiles against the revised module; canonical-map conclusion unchanged. |
| Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineBaseChangeComparison | unclaimed in local claims | Unchanged source compiles against the revised module; canonical-map hypothesis unchanged. |

No adapted module is delivered, and no module owned by another group is edited.

## Status

landed 20261012T215152-L-1303331 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial)
