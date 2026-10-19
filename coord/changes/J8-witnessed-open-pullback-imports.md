# WeilConjectures.witnessed_open_pullback

## Reason

Remove redundant imports after proving the theorem using the existing fixed-scalar
exact functor APIs. The conclusion structure, theorem signature and definitions are
unchanged. No downstream module imports this item in the current source graph.

## Old

```lean
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
```

## New

```lean
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 | Same signatures and structure, one theorem proved; redundant imports removed. |

The source import graph has no downstream users. A source scan also finds no use of
`WitnessedOpenPullbackData` or `witnessed_open_pullback` outside this module.
No target statement or definition changes. No consumer adaptation is required.

## Status

landed 20261019T231222-L-562341 2026-10-19 (merge of deliver/J8/Sheaf.Paper.TrfWitnessedOpenPullback)
