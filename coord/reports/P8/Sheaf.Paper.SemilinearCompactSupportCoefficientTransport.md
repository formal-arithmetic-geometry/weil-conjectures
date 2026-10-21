## What changed

Filled proof bodies for quotient-transition compatibility, derived-unit naturality,
additivity of the ordinary system limit, whole-system limit-unit naturality,
the section-normalized ordinary direct-image comparison, the projection-normalized
ordinary limit comparison, and the two zero-preservation
statements. The limit comparison is assembled from preservation of limits by scalar
restriction and the existing strict tower comparison. Proved private categorical
helpers isolate these arguments from the concrete completed ring constructions.
The ordinary direct-image comparison uses the coefficient-map naturality square
and composition of module pushforwards, with identity on all sections.
All existing public signatures, definitions and public imports are retained.

## Proved and sorry left

Closed eight original holes (no new holes):
- `scalarQuotients_commute`
- `systemRestrictionPush_existsUnique`
- `rightUnitApp_naturality`
- `ordinarySystemLimit_additive`
- `limitUnitApp_naturality`
- `ordinaryLimitRestriction_existsUnique`
- `systemRestrictionLimit_zero`
- `systemLimitRestriction_zero`

Five original holes remain, unchanged:
- `systemRestrictionPullInv_isIso`
- `systemRestrictionPush_isIso`
- `systemRestrictionOpenInv_isIso`
- `restrictionTower_existsUnique`
- `limitRestriction_existsUnique`

Every name above is in `WeilConjectures.CompactSupportCondensedRealization` and
belongs to `def-pur-semilinear-compact-support-coefficient-transport`.
No split-off statements or new axioms are introduced.

## No longer needed

No node or module is withdrawn. The existing public imports provide the constructions appearing in signatures
and definitions; the original proof import is retained. A private import exposes the proved
constant-ring naturality lemma in `VaryingRingOperations`. The experimental private
Mathlib limit-cone import was removed after the abstract helpers eliminated its need.

## Where the brief, the DAG or earlier work was wrong

The item node is a definition node with an empty proof and proof-dependency list;
the individual theorem docstrings supply the proof plans used here. No statement
or definition defect is asserted. The ordinary limit theorem uses the existing
`restrictionTower` theorem without reproving it. The remaining geometric and tower
normalization arguments have not been counted as closed.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
