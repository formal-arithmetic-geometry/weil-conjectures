# AlgebraicGeometry.ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality

## Reason

The main hole is decomposed into the smooth-triple cocycle/source-etale step and primitive
open-restriction step, with actual proofs for sigma invertibility, Cartesian sigma/source
base change, and finite-expression induction. These require different private proof imports.
The concrete module-sheaf tensor instances are costly to unify while unfolding; the proof
caches their existing definitions using local irreducibility, as SmoothExceptionalTensorPasting
already does. These attributes and elaboration options affect proof elaboration in this file
only. Every existing public signature, definition, and public import is unchanged.

## Old

```lean
import Sheaf.Paper.CompositionTensorMate
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.FiniteSiteCounitProjectionTransport
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
```

## New

```lean
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import Sheaf.Paper.SmoothExceptionalTensorPasting
import Sheaf.Paper.DualizingCocycleSourceEtale
import Sheaf.Paper.DualizingPrimitiveOpenRestriction
```

Immediately before the proved private helpers, after all existing definitions:

```lean
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The invertibility and normalized source-base-change helpers locally restore
`backward.isDefEq.respectTransparency false` to match the original coefficient-unit
expressions; other proof helpers use the settings above. A generic coefficient-category
helper proves pullback-compositor transport before specialization, avoiding repeated
expansion of concrete tensor instances. The extra universe `v` is used only by that
private helper.

These settings are not imported by consumers. No definition body is changed, and no data
is chosen from a new existence theorem. The new statements contain only proofs, and their
full sources and proofs in words are in their docstrings and DAG nodes. The main theorem's
statement and the meanings of all Challenge declarations are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.DualizingSigmaCocycleLocality --uses
AlgebraicGeometry.ProEtale.DualizingLocality.pullSquare` lists the two downstream modules
below; the only direct references to pullSquare are in the item itself. Neither downstream
module is edited or needs a forced adaptation, because its public imports, declarations,
and instance visibility do not change. Existing proof-only imports were not re-exported.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed in local claim records | Identical public signatures and definitions; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed in local claim records | Identical public signatures and definitions; no adaptation. |

## Status

landed 20261025T122714-L-1798478 2026-10-25 (merge of deliver/D4/Sheaf.Paper.DualizingSigmaCocycleLocality)
