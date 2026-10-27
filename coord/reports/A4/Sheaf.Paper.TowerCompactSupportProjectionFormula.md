## What changed

Reduced `AlgebraicGeometry.ProEtale.SpTowerProjection.openMap_evaluation` to the
normalization of the specified derived open-adjunction unit. Added a private
categorical calculation: transpose the evaluated arrow, use tensor-evaluation
naturality, substitute the normalized unit, and cancel the tensor, inverse-image
and open-extension comparison isomorphisms. The resulting arrow is exactly the
existing `finiteOpenMap`, with its existing direction and normalization.

Added `Sheaf.Paper.TowerOpenAdjunctionEvaluation` with the unit-normalization
statement alone, imported privately by the item. All existing public signatures,
definitions and public imports are preserved. The proper evaluation proof and
main invertibility theorem are unchanged.

Validation through lcompile.py: the final unit-normalization module compiled
cleanly in 57.2 seconds, and the final item compiled cleanly in 18.0 seconds.
Temporary profiling options have been removed. Both files meet the 100-character
line limit.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.SpTowerProjection.openMap_evaluation`
(node `lem-sp-tower-compact-support-projection-formula`) by decomposition.

The original hole
`AlgebraicGeometry.ProEtale.SpTowerProjection.tower_compact_support_projection_formula`
remains unchanged in the item module.

Added one hole:
`AlgebraicGeometry.ProEtale.SpTowerShriek.open_adjunction_unit_evaluation`
(node `lem-sp-tower-open-adjunction-unit-evaluation`). This states only the derived
open unit's evaluation equation, without tensor, projection arrows, compactifications,
constructibility, Tor bounds or invertibility. One of the item's two original
holes is reduced to one strictly smaller hole. This is a decomposition, with zero
net holes closed; the item has one hole and the new module has one hole.

## No longer needed

No existing import, node or module is withdrawn. The open evaluation calculation
needs only the unit equation: it does not need a separate counit-normalization
hypothesis, finite projection invertibility, constructibility or tensor bounds.
The main projection theorem is untouched, so its uniform-domain and finite-level
projection dependencies remain needed. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

`Sheaf.Paper.TowerProjectionDomainEvaluation` imports this item and calls
`openMap_evaluation`. Consequently, it cannot be imported here to prove this
unconditional evaluation identity. The reduction uses the specified open unit
and comparison maps directly, without an import cycle or detection of equality
by evaluation. No statement dispute or change of mathematical hypotheses.

## New nodes

`lem-sp-tower-open-adjunction-unit-evaluation` records the derived unit equation
obtained by localizing `Open.unit_evaluation` using `Open.unit_termwise` and the
specified inverse-image and open-extension comparisons. Its source is paragraph
(3) of the current blueprint integral direct-image proof, together with the
recorded ordinary unit and termwise localization. It is strictly part of the
open projection argument and is independent of the tensor calculation now
proved in the item.

Searches included LeanFinder, Loogle, Mathlib grep and local declaration/DAG
searches. The ordinary etale/pro-etale open comparison unit normalization and the
sectionwise pro-etale restriction unit concern different adjunctions; neither
states this derived system-to-level normalization. Generic localization unit
formulas do not identify these concrete comparisons. Identity immersions, empty
schemes, zero complexes and the first positive coefficient level satisfy the
same equation; ramification changes only the coefficient ring and imposes no
extra hypothesis. No change record is needed because existing interfaces are
unchanged.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
