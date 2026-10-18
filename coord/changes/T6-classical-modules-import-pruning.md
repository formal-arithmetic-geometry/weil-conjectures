# AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules

## Reason

Prune imports after proving the module comparison using the existing generic coefficient
API. The broad source Comparison import includes derived base-change and acyclicity
material that this ordinary-sheaf theorem does not use. Keep the narrower FullyFaithful
import as a proof import. Other removed direct public imports are redundant through
retained statement imports. The theorem signature is verbatim unchanged, and no definition
or target statement changes meaning. The new helpers are private and proved; their Kan
preservation evidence is installed locally rather than as a global instance.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules --uses
proEtaleClassicalSheavesModules` lists the following four consumers. No consumer text
mentions the theorem yet; their proofs remain separate work. The import-prune check
passed against the completed module. The fixed coefficient API remains supplied by the
retained `ProEtaleSiteComparison` import, and `ClassicalContinuityMap` publicly imports
`ProEtaleDerivedCategory`, `RingedSiteModules` and the ordinary constant-sheaf infrastructure.
No consumer signatures, statements or proofs are edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules` | T6 | The theorem signature and statement imports required by it stay; unused public imports are removed. |
| `Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal` | E5 | No adaptation: existing statement imports remain available through retained imports or the consumer's own imports; no declaration used by its Lean text is removed. |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom` | F5 | No adaptation: existing statement imports remain available through retained imports or the consumer's own imports; no declaration used by its Lean text is removed. |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType` | F6 | No adaptation: existing statement imports remain available through retained imports or the consumer's own imports; no declaration used by its Lean text is removed. |
| `Sheaf.Paper.BoundedBelowCtfReflection` | unclaimed | No adaptation: existing statement imports remain available through retained imports or the consumer's own imports; no declaration used by its Lean text is removed. |

## Status

landed 20261018T145117-L-3645529 2026-10-18 (merge of deliver/T6/Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules)
