# CompletedTargetAugmentationNormalization import pruning

## Reason

The normalized scheme API proves the two original holes without directly importing
its general categorical construction modules or the unrelated Qbar pullback interface.
Retain the protected ringed tower-limit comparison proof import. All names used by
the unchanged statements are publicly available through the three retained public
imports. The module also sets backward elaboration transparency options to handle
the definitionally equal completed-pullback codomains in categorical rewrites.
These options introduce no declarations or mathematical assumptions.

## Old

```lean
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.ReductionPullbackDerivedTower
public import Sheaf.Paper.AugmentedDiagramProjectionMate
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
```

## New

```lean
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
```

Added elaboration options:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedTargetAugmentationNormalization | U7 | Both statements unchanged; two proofs filled; redundant imports removed. |

`tools/downstream.py Sheaf.Paper.CompletedTargetAugmentationNormalization` reports
no downstream modules. The item retains its Lean attachment and DAG parents.
No declaration or definition used by a target changes, and no source-library file
is modified. Names from redundant imports which remain transitively reexported are
still available; the unrelated Qbar interface ceases to be reexported by this item.

## Status

landed 20261023T135705-L-2959055 2026-10-23 (merge of deliver/U7/Sheaf.Paper.CompletedTargetAugmentationNormalization)
