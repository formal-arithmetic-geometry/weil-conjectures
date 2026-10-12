# Sheaf.CategoryTheory.BoundedBelowCoproductFiltration imports

## Reason

The second reading removes the unused proof imports ExactCoupleMorphism and
TruncationHypercohomology from the item. The latter belongs to the new construction
obligation's plan and is imported privately there. Replace the broad public
TStructure import by HomologySequence, which declares the homology functor in the
existing public signature, and remove redundant public EnoughInjectives. The
existing KInjectiveResolution import supplies the resolution instance used to
elaborate the derived functor, and Products is retained for the coproduct signature.

No existing declaration's signature, definition, instance or docstring changes.
This record is for the removal of public imports, required by the delivery
preflight. No target statement or definition changes meaning.

## Old

```lean
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.TruncationHypercohomology
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.CoproductTruncationCouple
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.BoundedBelowCoproductFiltration --uses
exists_boundedBelow_coproduct_filtration` finds exactly the two rows below.
The module has one direct importer (667 transitive importers at this checkout).
The direct importer privately imports the item and already publicly imports
TStructure itself. Its unchanged source compiled against the delivered modules
with lcompile.py in 38.1 seconds. No forced adaptation is necessary, and no other
module is included in the delivery. No changed declaration propagates to any
transitive user. Only the maintainer performs the global build.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.BoundedBelowCoproductFiltration | R1 | Import cleanup; unchanged public theorem signature; local compile passes. |
| Sheaf.AlgebraicGeometry.TruncatedDirectImageSheafCoproductEpi | unclaimed in the local claims snapshot | Uses the unchanged theorem; imports TStructure explicitly; unchanged source compiles against delivery; no adaptation. |

## Status

landed 20261012T184336-L-4017367 2026-10-12 (merge of deliver/R1/Sheaf.CategoryTheory.BoundedBelowCoproductFiltration)
