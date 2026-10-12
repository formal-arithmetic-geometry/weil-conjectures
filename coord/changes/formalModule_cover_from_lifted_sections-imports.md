# AlgebraicGeometry.formalModule_cover_from_lifted_sections

## Reason

Remove the unused public import of the sheaf tensor-product extension module.
All tensor products and natural-number tensor powers in the existing theorem
are supplied by the already public invertible-module import. The removed module
adds change-of-rings and positive tensor powers, which this theorem and its proof
do not use. The theorem and every definition retain their signatures and visibility.
The added helper imports are proof-only. No target or target-used definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.AlgebraicGeometry.FormalTwistedTransitionSections
import Sheaf.AlgebraicGeometry.CoherentCoverFromCompatibleTwistedSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.CategoryTheory.Functor.OfSequence
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | The only direct importer. Calls the unchanged cover theorem; does not use the removed module's change-of-rings or positive-tensor-power declarations. No adaptation is required. |

The original sole direct importer was compiled unchanged against the new sandbox
overlay using lcompile.py and passed in 3.5 seconds; no adaptation is required.

The user's remaining transitive callers receive no changed theorem or definition.
The only direct importer imports this module privately. It uses ordinary tensor
powers, already supplied by its other proof imports, rather than the removed module.

## Status

landed 20261012T232902-L-2042689 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.FormalModuleCoverFromLiftedSections)
