# Sheaf.Paper.IntegralDerivedReduction imports

## Reason

Remove four redundant direct public imports after proving all three holes. Their modules
remain in the public closure of the retained imports, so every previously exported module
remains exported. A traversal of public import edges gives exactly the same module set
before and after. The independent-coefficient K-flat resolution import is deliberately
retained because removing it would shrink that interface. The new constant-to-completed
map import is needed only by the local-surjectivity proof and is private.

No declaration type, definition, instance registration, or mathematical convention changes.

## Old

```lean
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
```

## New

```lean
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
```

## Users

All direct importers are listed below. No consumer is edited, so their current ownership
is immaterial to this delivery. The public import closure is identical for the item and
hence for every consumer, including indirect consumers. Existing statements and data are
unchanged; every declaration keeps its exact signature and visibility.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GeometricStalkPerfect | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralConstructibleTriangulated | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralDerivedOperations | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralHomReduction | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralHomReductionComparison | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralReductionTowerWellDefined | not adapted | identical exported modules and signatures |
| Sheaf.Paper.IntegralScalarExtension | not adapted | identical exported modules and signatures |
| Sheaf.Paper.PurTwistSheafLocallyFree | not adapted | identical exported modules and signatures |
| Sheaf.Paper.ResidueLisseProjectiveModels | not adapted | identical exported modules and signatures |

No target statement or definition changes. All transitive importers have the same public
modules available by the same reachability argument.

## Status

landed 20261019T192649-L-1852378 2026-10-19 (merge of deliver/B4/Sheaf.Paper.IntegralDerivedReduction)
