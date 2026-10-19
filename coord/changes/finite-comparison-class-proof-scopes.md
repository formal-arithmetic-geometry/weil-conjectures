# AlgebraicGeometry.ProEtale.exists_fixedComparisonClassAdjunction

## Reason

Replace the existential theorem's proof hole by the comparison Hom chain, descent along the
comparison equivalence, and compactification coherence. The static interface checker also
records the section, universe, variable and namespace commands used by the new private proof
helpers. These commands are scoped to this file. All four helper instances are explicitly
private and local, so their registrations do not affect downstream typeclass search.

## Old

The existing context immediately after `set_option autoImplicit false` was:

```lean
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
```

The theorem's whole proof was `by sorry`. Its signature and all public definitions are retained.

## New

Before that unchanged context, the proof adds `section HomDescent`, with locally bound category
universes and variables inside `namespace CategoryTheory`, and closes both scopes before
`universe u`. Its definitions and theorems are private. The other new helpers are private within
`namespace AlgebraicGeometry.ProEtale`. The instance registrations have these literal heads:

```lean
private local instance comparisonOriginLift_full
private local instance comparisonOriginLift_faithful
private local instance comparisonOriginLift_essSurj
private local instance comparisonOriginLift_isEquivalence
```

The complete declarations are in the delivered module. They establish the equivalence between
bounded-below etale complexes and the full subcategory of their essential image. No existing
signature, public import, definition body, visibility or target meaning changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction --direct` lists
the eight direct importers below. Its transitive closure contains 406 modules. No downstream
module names a new private helper; every existing public declaration and public import remains
identical, so their statements have the same meaning. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | No interface change |
| Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass | unclaimed | No interface change |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | No interface change |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No interface change |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | No interface change |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | No interface change |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No interface change |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No interface change |

## Status

landed 20261019T005259-L-2747609 2026-10-19 (merge of deliver/G2/Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction)
