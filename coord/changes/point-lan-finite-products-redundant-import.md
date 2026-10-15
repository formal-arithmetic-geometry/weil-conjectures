# AlgebraicGeometry.ProEtale.point_lan_finite_products

## Reason

Remove a redundant public product import while proving the target. The unchanged
public import `Sheaf.Paper.ProfiniteTestObjectFunctor` itself publicly imports
`Mathlib.CategoryTheory.Limits.Shapes.Products`. Thus the same product declarations
remain publicly available. A source traversal checked that the complete set of
publicly reachable repository modules is identical before and after the edit.
The target signature and all existing definitions remain byte for byte unchanged;
no target meaning or target review is reopened. This record is required by the
delivery checker for any public import removal.

## Old

```lean
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.ProEtalePointComponentsMaps
```

## New

```lean
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Sheaf.Paper.ProEtalePointComponentsMaps
```

## Users

All transitive downstream modules from `tools/downstream.py` are listed below;
holders are the recorded claims at the second reading. None is modified.
Only `Sheaf.Paper.PointLanAffineEvaluation` directly imports this module and uses
`point_lan_finite_products`; it already publicly imports the product module itself.
No user gains or loses a hypothesis, conclusion, definition, or public dependency.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | B3 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | B3 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | C2 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | A4 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.PointLanAffineEvaluation | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleSheafificationWcontractibleSections | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Public product API remains available; statement and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Public product API remains available; statement and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Public product API remains available; statement and definitions unchanged; no adaptation. |

## Status

landed 20261015T192134-L-1051309 2026-10-15 (merge of deliver/E1/Sheaf.Paper.PointLanFiniteProducts)
