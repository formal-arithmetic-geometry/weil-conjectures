# CategoryTheory.siteLeray_degenerate imports

## Reason

The proof constructs the pushed-forward injective resolution and compares section
complexes. It needs neither pullback on cohomology nor uniqueness of auxiliary lifts.
Remove the unused broad public import of SiteCohomologyPullback, replacing it by the
Mathlib imports necessary to type the same existing statement. No declaration signature,
universe, definition used by a target, or existing visibility changes. The sole direct
importer already imports SiteCohomologyPullback independently; it compiles unchanged.

## Old

```lean
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
```

## New

```lean
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.SiteLerayDegenerate | V1 | Same signature; proved; narrower public imports. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | ORCHESTRA | Sole direct importer, via a proof-only import. It separately imports SiteCohomologyPullback. Original file compiled unchanged against the delivered module; no adaptation. |

`tools/downstream.py Sheaf.CategoryTheory.SiteLerayDegenerate --uses siteLeray_degenerate`
lists 131 transitive importers and no downstream textual user of the declaration.
The direct import is proof-only, so downstream public statement interfaces do not
inherit the removed import through that module. None of their statements changes.
There are no adapted modules in this delivery; the temporary identical importer copy
used for the compiler check has been removed from the delivery's source set.

## Status

landed 20261012T135326-L-1697097 2026-10-12 (merge of deliver/V1/Sheaf.CategoryTheory.SiteLerayDegenerate)
