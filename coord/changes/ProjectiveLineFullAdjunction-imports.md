# Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction imports

## Reason

The normalized datum already contains the adjunction and its counit equation.
Only ProjectiveLineTrace is needed directly. Its public imports supply all declarations
used by this statement. The theorem signature and all definitions remain unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProperStability
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Sole direct importer; its import of this item is private, and it already directly publicly imports all five removed public imports. Its statement and public exports are unchanged; compiled against this delivery in 6.8 seconds on 2026-10-19. |

All transitive downstream modules are reached through this sole private import, so they
never received this item's public imports through that edge. No definition or target
statement changes meaning, and no consumer adaptation is required.

## Status

landed 20261019T005339-L-2755103 2026-10-19 (merge of deliver/M1/Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction)
