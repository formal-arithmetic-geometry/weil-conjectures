# ProEtaleSheafificationWcontractibleSections redundant public import

## Reason

The second reading found that `Mathlib.CategoryTheory.Sites.LeftExact` is a redundant
public import. All its exports remain publicly available through the unchanged chain
`PointLanAffineEvaluation` -> `ProEtalePointComponentsMaps` ->
`ProfiniteTestObjectFunctor` -> `ModuleObject.Basic` -> `ModuleObject.UpperLowerStar.Monoidal`
-> `FiniteCoefficient.UpperLowerStar.Monoidal` -> `Sites.Monoidal` -> `Sites.Pullback`
-> `Mathlib.CategoryTheory.Sites.LeftExact` (the intermediate source modules are in
`WeilConjectures`). The new ordinary import of `Sites.LocallyBijective` is redundant too.
Removing both leaves the module compiling cleanly. No declaration signature, data
construction, definition body, instance or target meaning changes.

## Old

```lean
public import Sheaf.Paper.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
```

## New

```lean
public import Sheaf.Paper.PointLanAffineEvaluation
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleAffineContractibleExtension
```

## Users

`tools/downstream.py` found the following 16 transitive importers. Its `--uses`
checks found no downstream textual use of either declaration yet. The sole direct
importer is `Sheaf.Paper.CondensedPointBasisEvaluation`; its unchanged source is
checked against the revised compiled module. Holders are the local claim snapshot.
There are no forced adaptations. Every former public import is still in the public
transitive closure, so downstream statements and target meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProEtaleSheafificationWcontractibleSections` | E2 | Only redundant imports removed; signatures and definition unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | B3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | B3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedPointBasisEvaluation` | D3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | C2 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | C4 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | No adaptation; all previous exports remain publicly reachable. |
| `TargetsCheck` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | No adaptation; all previous exports remain publicly reachable. |

## Status

landed 20261015T183130-L-811809 2026-10-15 (merge of deliver/E2/Sheaf.Paper.ProEtaleSheafificationWcontractibleSections)
