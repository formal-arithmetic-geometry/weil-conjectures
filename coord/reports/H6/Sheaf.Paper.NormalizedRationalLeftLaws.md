## What changed

Split the original normalized rational left laws theorem into two strictly smaller named
component theorems, one for scalar composition and one for the scalar identity. The parent
now combines these component theorems by conjunction. The component proofs remain explicit
named obligations with their source argument recorded in their docstrings.

## Proved and sorry left

The parent theorem is assembled from the two component statements. The two component
proofs remain `sorry`:

- `normalized_rational_left_composition` (`lem-sf-normalized-rational-left-composition`)
- `normalized_rational_left_identity` (`lem-sf-normalized-rational-left-identity`)

No definitions contain `sorry`.

## No longer needed

No imports or existing DAG dependencies were pruned. The parent proof now depends only on
the two split component nodes; the earlier undecomposed proof dependency list is replaced by
those component nodes.

## Where the brief, the DAG or earlier work was wrong

The original node bundled two independent localization laws into one theorem while its
proof plan separately describes composition and identity. The split makes those obligations
explicit and strictly smaller, preserving the exact target statement and hypotheses.

## New nodes

Added `lem-sf-normalized-rational-left-composition` and
`lem-sf-normalized-rational-left-identity`, each in its own module under `lean/Sheaf/Paper`.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
