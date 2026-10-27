## What changed

The target theorem now assembles a full `Presentation` from a partial normalized
comparison record and a separate Milnor-invertibility theorem. Added the modules
`Sheaf.Paper.DiagonalTraceComparisonPartial` and
`Sheaf.Paper.DiagonalTraceComparisonLimitIsos`, and imported both privately for the
proof. The record assembly itself is complete and field by field.

## Proved and sorry left

Proved: `exists_diagonalTraceComparisonPresentation`.

Sorry left: `exists_diagonalTraceComparisonPartial` (node
`new-sfb-diagonal-trace-comparison-partial-existence`) and
`diagonalTraceComparisonLimitIsos` (node
`new-sfb-diagonal-trace-comparison-limit-isos`). The `PartialPresentation` definition
has no sorry.

## No longer needed

The original seven proof-dependency nodes are no longer imported directly by the
target proof; their work is represented by the two strictly smaller split-off
theorems. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG described a direct construction of every field in one theorem, but no
constructor theorem for the combined record exists in the imported library. The
geometric/derived construction and the Milnor invertibility argument are independent
parts, so they were split into named statements before the final record assembly.

## New nodes

Added `new-sfb-diagonal-trace-comparison-partial`, the partial record definition,
`new-sfb-diagonal-trace-comparison-partial-existence`, and
`new-sfb-diagonal-trace-comparison-limit-isos`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
