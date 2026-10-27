# AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorProduct

## Reason

Remove unused public imports from the item. Its scheme module category and monoidal
structure are supplied by the other existing statement imports. This removes unnecessary
exposure of general ringed-site and independent-universe cochain tensor infrastructure.
The theorem's name, binders, universe, conclusion and visibility are unchanged.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| No direct Lean importers in the current source tree | none | No adaptations required |

The DAG parent `lem-trf-invertible-fp-tensor-models` continues to use the unchanged
statement; its unfinished proof has not yet imported this module. No existing module
other than the item is changed, and no target statement or definition changes meaning.

## Status

landed 20261027T094509-L-235074 2026-10-27 (merge of deliver/R8/Sheaf.AlgebraicGeometry.Modules.FinitePresentationTensorProduct)
