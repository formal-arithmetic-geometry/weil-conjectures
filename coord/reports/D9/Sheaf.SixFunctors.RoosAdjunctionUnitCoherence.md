## What changed

Proved `CategoryTheory.RoosAdjunctionUnit.roosAdjunctionUnitCoherence` with its
statement and all existing public declarations unchanged. Added only proved private
helpers in its module. Constructed both kappa maps from the existing canonical
additive Roos comparison, and descended their conjugates to lambda by fully faithful
restriction along localization. The derived-unit equation is proved as an equality
of natural transformations on the actual derived category. The explicit strict
augmentations and their zero signed coordinates are retained.

Updated the item node's proof, proof dependencies and proof origin to record this
route. No source-library file or downstream interface changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.RoosAdjunctionUnit.roosAdjunctionUnitCoherence`
(node `lem-sf-roos-adjunction-unit-coherence`).
Holes closed: 1. Holes added: 0. Holes left in delivered modules: 0.
No decomposition and no new nodes. The complete item compiles cleanly through
`lcompile.py` (52.7 seconds), with no errors or warnings. Both new private proof
imports pass `tools/import_direction.py may`; all lines have at most 100 characters.

## No longer needed

Removed proof imports `Sheaf.Paper.ExactProductFunctorStrictLimit` and
`Sheaf.CategoryTheory.StrictRoosComparison`. Their aggregate statements
`lem-cbc-exact-product-functor-strict-limit` and `lem-weil-strict-roos-comparison`
are not needed directly: the smaller proved `strictRoosDerivation` supplies the
normalized derived functor, and the canonical additive comparison supplies chain
naturality, horizontal coherence and augmentations. The ordinary-limit comparison,
resolution formulas and triangle formulas bundled by ExactProductFunctorStrictLimit
are not needed for the equations in this item. Removed their obsolete tool-use
entries from this item's node. This does not withdraw either module or any other
parent's use of them.

Added proof imports `Sheaf.CategoryTheory.StrictRoosDerivation` and
`Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence`. The unit and chapter route
is unchanged; these are generic tools below the unit's open-factor calculation.
All existing public imports are retained because they support the public interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The planned elementary chain-coordinate
calculation is already available as horizontal coherence for the canonical Roos
comparison: specializing it to the inverse adjunction unit and cancelling gives
exactly the needed equation. The full aggregate strict-limit theorem is therefore
unnecessary here. The proof also obtains the eta/theta normalization on every
complex, which specializes to the unchanged K-injective conclusion.

Edge cases are covered by the general calculations: zero complexes and zero
augmentations, identity functors with any invertible unit, arbitrary transitions,
and unbounded degrees. All constructions use the fixed shifted cone; no arbitrary
cone filler or new definition chosen from an unproved existence theorem is used.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
