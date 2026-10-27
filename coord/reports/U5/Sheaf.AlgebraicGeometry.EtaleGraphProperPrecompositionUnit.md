## What changed

The parent theorem now reduces natural-transformation equality to its objectwise component.
The component calculation is recorded in the new module
`EtaleGraphProperPrecompositionUnitKInjective` and left as a named proof obligation.

## Proved and sorry left

Closed `graph_proper_precomposition_unit` by natural-transformation extensionality and
the objectwise component theorem. One new sorry remains in
`graph_proper_precomposition_unit_component`.

## No longer needed

None. All original imports remain available to the split component calculation.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the full natural-transformation equality as one geometric
calculation. The Lean reduction first needs the objectwise component statement; the DAG now
records that split explicitly.

## New nodes

`lem-pur-graph-proper-precomposition-unit-component`.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
