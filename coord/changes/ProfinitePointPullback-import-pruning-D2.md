# ProfinitePointPullback import pruning

## Reason

Remove unused or redundant direct imports from `Sheaf.Paper.ProfinitePointPullback`.
The proof-only `TensorProductOfUniverses` import contributes no declaration used by this module.
The three redundant public imports are already public imports of the retained
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, so all their exported declarations remain
available to importers. Every existing signature, definition, visibility and docstring remains
identical. No target statement or definition changes, and no target review is reopened.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
```

Other original imports remain.

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
```

The retained module publicly imports each of the three removed public imports. The removed
proof-only import was never re-exported. The module compiles without these four direct imports;
all 28 public declarations have only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## Users

The read-only `tools/downstream.py Sheaf.Paper.ProfinitePointPullback` query lists the following
22 transitive importers. Each retains every original declaration and public import through
`ProEtaleInverseImage`; no downstream statement or proof needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProfinitePointPullback` | D2 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | J1 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | G2 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | A4 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | H3 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedPointBasisEvaluation` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | C2 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | A4 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.Paper.GeometricFieldProEtaleEvaluation` | E4 | Same statements, definitions, and publicly available imports; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | Same statements, definitions, and publicly available imports; no adaptation. |
| `TargetsCheck` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Same statements, definitions, and publicly available imports; no adaptation. |

## Status

landed 20261016T054832-L-155254 2026-10-16 (merge of deliver/D2/Sheaf.Paper.ProfinitePointPullback)
