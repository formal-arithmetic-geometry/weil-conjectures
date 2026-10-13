# CoherentIntegralGenericIdealMonoImports

## Reason

The completed proof uses no coherent-kernel, quasi-coherent-image, generic-ideal
criterion, or stalk-exactness theorem. Remove their imports to prune those proof
branches. Three of these proof dependencies had been imported publicly, so this
removes their re-exports. Retain direct public imports for every notion in the
unchanged theorem signature: coherence, stalk functor, Noetherian schemes, and
ideal sheaves. The new Mathlib proof imports remain private.

No definition or declaration signature changes. No target meaning changes.
The sole direct importer, `CoherentIntegralGenericIdealMap`, already imports all
three removed public dependencies itself, and already publicly imports both
replacement statement modules. Thus it needs no forced adaptation.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
public import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
public import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.Algebra.Homology.ModuleStalkExact
```

## New

```lean
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.CategoryTheory.Preadditive.Biproducts
```

The new private proof helper uses `open Opposite TopologicalSpace` inside the
existing namespace; these are name-resolution commands, not exported declarations.
A scoped unused-variable linter option at the original theorem keeps its coherence
hypotheses verbatim. The original theorem statement is unchanged.

## Users

`tools/downstream.py --uses mono_of_coherent_ideal_sum_generic_iso` lists the item
and its sole direct user. The 264 transitive downstream modules inherit no changed
statement or definition. Since the direct importer already supplies every removed
public import independently, none of them requires an adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMono | T1 | Complete proof; prune proof imports; unchanged signature. |
| Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMap | unclaimed | Identical theorem application; independently imports all removed and replacement public imports. |

## Status

landed 20261013T024049-L-3339392 2026-10-13 (merge of deliver/T1/Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMono)
