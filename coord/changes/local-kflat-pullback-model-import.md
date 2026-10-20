# Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel

## Reason

The quarantined item imported `Sheaf.AlgebraicGeometry.DerivedPullback`, which is
withdrawn and contains no declarations. The proof uses the adopted source-library
declaration `AlgebraicGeometry.derivedPullback`, so the public import must point to
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. Unused public imports are also
removed after checking that the theorem still compiles.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |
| `Sheaf.AlgebraicGeometry.ResidueRankModelDifferential` | quarantined/unclaimed | Imports this item; theorem interface is unchanged. |

## Status

landed 20261020T211619-L-3478615 2026-10-20 (merge of deliver/A4/Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel)
