# Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion imports

## Reason

The proof and statement do not use strict henselization. Its public import supplied the
geometric-point declaration and abelian coefficient instances indirectly. Import their
providers directly to remove the strict-henselization dependency. This changes only imports
and the proof of the existing theorem; its full Lean signature remains verbatim.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
```

## Users

`tools/downstream.py` finds 486 transitive importers and exactly one direct importer.
With `--direct --uses isZero_higherDirectImage_iff_geometric_cohomology_colimits`, the
only declaration-name occurrence is the theorem itself: the direct consumer currently has
an unproved theorem and an unused proof-dependency import. Its import of this module is
private, so this edge exposes none of the removed declarations to its own consumers.
The theorem statement and all definitions remain unchanged; no target changes meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion | M1 | Same theorem signature, proved; narrower import interface. Compiles cleanly. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | C3 | Original source is compiled against the revised item, without edits; its statement uses no removed declarations. No adaptation delivered. |

## Status

landed 20261018T062828-L-661649 2026-10-18 (merge of deliver/M1/Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion)
