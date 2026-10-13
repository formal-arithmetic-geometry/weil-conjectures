# depth_two_hartogs_algebra_comparison: import pruning

## Reason

The theorem is about an arbitrary morphism f, not a finite or etale morphism.
Neither its signature nor its proof needs the finite or etale imports. Remove
these unused imports while adding the two proof-only dependencies of its reduction.
The delivery also introduces the sourced Hartogs restriction theorem in its own
module; no existing declaration signature or definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth
public import Mathlib.Algebra.Category.ModuleCat.Stalk
```

The original item proof is `:= by sorry`; its theorem signature is unchanged.

## New

```lean
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
```

The replacement proof uses the restriction unit, composition of pushforwards,
full faithfulness and the module stalk functor. The new module's declaration is
`AlgebraicGeometry.Scheme.isIso_restrictAdjunction_unit_of_depth_two`, whose full
signature is recorded verbatim in `lem-sbc-depth-two-hartogs-restriction.json`.
It is the sole new named sorry and leaves the hole count unchanged.

## Users

Ran `tools/downstream.py Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison
--uses depth_two_hartogs_algebra_comparison` and read the sole direct importer.
There are 119 transitive importers, but only the item and the direct importer
mention the declaration. The direct importer already publicly imports both
removed Mathlib modules, so its exported imports and those of every further
importer still contain them. No target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison | M2 | Unchanged signature and definitions; unused imports removed, proof-only imports added. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence | unclaimed | Imports Finite and Etale directly; unchanged source compiles against the delivered overlay. No adaptation needed. |

No existing module imports the new restriction module directly; the item imports
it only for its proof. All later importers inherit the same existing statements.

## Status

landed 20261013T072357-L-1122340 2026-10-13 (merge of deliver/M2/Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison)
