## What changed

The assigned theorem now performs a Boolean case split and applies the fixed-false
and fixed-true component theorems. Added the proof-only imports
`SfP1ProjectionTraceTransportFalse` and `SfP1ProjectionTraceTransportTrue`.
Added one new module and one new DAG node for each fixed component. The two
component proofs remain named public obligations because the geometric exchange
calculation is not available elsewhere in the library.

## Proved and sorry left

The assigned declaration `AlgebraicGeometry.Etale.SfP1Transport.projectionTraceTransport`
is proved by genuine case analysis from the two strictly simpler fixed-projection
statements. Two sorries were added by this decomposition:

- `projectionTraceTransport_false`, node `lem-sf-p1-projection-trace-transport-false`;
- `projectionTraceTransport_true`, node `lem-sf-p1-projection-trace-transport-true`.

No definition contains a sorry. The assigned module itself has zero sorries.

## No longer needed

No existing proof dependency is pruned. The original abstract geometric proof
dependencies remain the declared dependencies of each fixed component. The main
module uses only the two new component nodes for its proof.

## Where the brief, the DAG or earlier work was wrong

The earlier decomposition correctly isolated this equation from the trace
comparison, but the remaining theorem has no exact library lemma: the imported
chart exchange theorem concerns a different endpoint and does not identify the
ordinary-to-compact-support transport. A direct proof still requires the full
mate-pasting and normalized-twist calculation. The delivery therefore makes the
Boolean components explicit, each with a fixed projection and strictly fewer
cases, and assembles the original statement without changing its signature.

## New nodes

`lem-sf-p1-projection-trace-transport-false` states the first-projection component
and is carried by `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse`.

`lem-sf-p1-projection-trace-transport-true` states the second-projection component
and is carried by `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue`.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
