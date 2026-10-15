# Sheaf.Targets.EtaleSmoothRing imports

## Reason

The existing smooth-derived component theorem supplies the target proof directly.
Remove the unused coefficient equivalence and abelian exchange proof route. The
public imports needed by the target statement are supplied by the retained
public base-change morphism definitions and the two Mathlib imports. No
existing declaration signature or definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
```

The added derived smooth-base-change import is proof-only. No options,
notations, attributes, or declaration visibility are changed.

## Users

`python3 tools/downstream.py Sheaf.Targets.EtaleSmoothRing --uses
AlgebraicGeometry.Etale.isIso_baseChange_of_smooth_of_ring_order_invertible`
reports only `TargetsCheck` downstream. The declaration itself is mentioned only
in its defining module. A separate import-source search finds no other direct
importer and no importer of `TargetsCheck`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Targets.EtaleSmoothRing | A2 | Same byte-for-byte theorem signature; direct imports pruned. |
| TargetsCheck | maintainer | Imports the theorem module only; has no declarations or proofs using removed exports. No adaptation required. |

No definition used by a target is changed, so this does not reopen its statement
review. No adapted modules are included.

## Status

landed 20261015T154148-L-157707 2026-10-15 (merge of deliver/A2/Sheaf.Targets.EtaleSmoothRing)
