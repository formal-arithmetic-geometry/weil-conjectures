## What changed

Updated `Sheaf.Paper.FieldProjectionOriginWitnesses` so the target theorem is proved by
assembling named intermediate clauses. The proof obtains normalized coefficient-unit data,
then combines the levelwise origin, lower-bound, GoodLevel, and transport clauses into the
existing `WitnessLaws` conjunction. The module still uses its original imports because the
existing definitions in the module depend on them.

## Proved and sorry left

Proved `AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_witnesses`
(the original module sorry is closed). Five strictly smaller named statements remain as
sorries, each with a node and a complete proof plan: `field_projection_origin_data`,
`field_projection_origin_level_witnesses`, `field_projection_origin_lower_bounds`,
`field_projection_origin_good_levels`, and `field_projection_origin_transport`.

## No longer needed

No imports or proof-dependency nodes were pruned. The original definitions and their
supporting imports remain needed by the item module; the theorem route now depends on the
five split clause nodes recorded in the sandbox DAG copies.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan cannot be discharged directly from the currently declared
interfaces within this item. Its independent construction and four logical output clauses
were therefore split into named intermediate theorems. The target statement and all existing
definition signatures are unchanged.

## New nodes

Added `lem-sp-field-projection-origin-witnesses-data` for normalized coefficient-unit data,
`lem-sp-field-projection-origin-witnesses-levels` for the five levelwise origins,
`lem-sp-field-projection-origin-witnesses-lower-bounds` for the five lower bounds,
`lem-sp-field-projection-origin-witnesses-good-levels` for the GoodLevel conjunction, and
`lem-sp-field-projection-origin-witnesses-transport` for inverse dualizing-comparison
transport. Each node records the source paragraph and the dependencies used by that clause.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
