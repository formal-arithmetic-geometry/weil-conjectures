# AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice comparison data

## Reason

Extract the existing records and formula definitions from the item into a definition-only
module so that separately stated ordinary and derived proof steps can import their types
without an import cycle. All declarations keep their names, binders, universes, instances,
attributes and bodies. The item publicly imports the extracted module, which publicly
imports the same dependencies as before. No mathematical statement or definition changes.
This extraction serves a proof decomposition, not a compiler time-limit workaround.

## Old

The item contains the definitions from `Modules` through `DerivedComparison`, followed by
`component_slice_hom_comparison_test`. Its public imports are verbatim:

```lean
public import Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation
public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
```

## New

The definitions from `Modules` through `DerivedComparison` have identical signatures and
bodies in `Sheaf.AlgebraicGeometry.ComponentSliceComparisonData`. The item retains the
identical signature of `component_slice_hom_comparison_test` and reexports all extracted
declarations with:

```lean
public import Sheaf.AlgebraicGeometry.ComponentSliceComparisonData
```

The new data module retains all public imports listed above. Plain imports of unused
proof dependencies are removed. The original node now attaches its theorem alone; the
new definition node attaches all moved declarations. No definition data is chosen from a
new existence theorem. No target changes its meaning and no further target review is
needed for a change in mathematical definitions.

## Users

A search of all `lean/` for direct imports of the item returned no matches. Its unfinished
DAG parents remain dependencies of the item, and no module or DAG node is withdrawn.
The new ordinary and derived modules use the same extracted data directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComponentSliceHomComparison | K1 | Same exports and statement; complete assembly proof |
| Sheaf.AlgebraicGeometry.ComponentSliceOrdinaryMonoidal | K1, new | Imports the extracted data |
| Sheaf.AlgebraicGeometry.ComponentSliceDerivedNormalization | K1, new | Imports the extracted data |

## Status

landed 20261026T082337-L-2163875 2026-10-26 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ComponentSliceHomComparison)
