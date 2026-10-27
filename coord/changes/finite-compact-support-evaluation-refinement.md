# Finite compact-support evaluation refinement

## Reason

The finite evaluation theorem is already available for the associator-expanded
`RelativeCompactSupport.towerH` construction. The target uses the equivalent strict
`compositionE` presentation, so the compatibility and canonical ordinary maps are
recorded explicitly for the reduction.

## Old

`properExchange`, `ordinaryE`, and `evaluationF` used the local mate and evaluation
formulas. The target imported no relative compact-support compatibility module.

## New

These three definitions use the corresponding canonical `RelativeCompactSupport`
constructions, and the proof imports `Sheaf.Paper.CompositionExchangeTowerH`.

## Users

The finite evaluation theorem in the target module consumes these definitions. Existing
importers see the same categorical interfaces and the canonical implementations.

## Status

Implemented in the F4 stage-3 delivery; the split-off associator compatibility theorem
remains a named follow-up statement with one `sorry`.
