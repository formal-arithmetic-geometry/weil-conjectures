## What changed

Proved `finiteActionCompatibleLimit` in
`lean/Sheaf/Topology/FiniteActionCompatibleLimit.lean`, preserving its statement,
public imports, and definitions. The proof uses the Mathlib instances for finite
spaces, products, and subspaces. It writes the compatibility locus as an
intersection of closed equalizers, obtains its compactness from
`IsClosed.isCompact`, constructs the coordinate action using `r_smul`, proves the
action laws coordinatewise, and proves continuity through the product and subtype
topologies. This implements the existing six-step DAG plan using Mathlib's APIs.

## Proved and sorry left

Closed the sole hole: `finiteActionCompatibleLimit`
(node `lem-sfb-finite-action-compatible-limit`). Added zero holes; none remain.
The proof permits empty stages and an empty compatibility space: no point or
surjectivity witness is chosen. It works for nondirected partial orders.

## No longer needed

None. No imports, nodes, or modules are removed. Both declared proof dependencies
remain used through their Mathlib matches: `Pi.compactSpace` for
`lem-weil-pbc-tychonoff-product-quasi-compact` and `IsClosed.isCompact` for
`lem-weil-pbc-closed-in-quasi-compact`. No additional Sheaf imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The transition identity and composition laws
are not required for these topological properties or the restricted action;
they remain in the unchanged statement. Closed equalizers give the existing
closed-cylinder argument directly via the continuous maps from discrete stages.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
