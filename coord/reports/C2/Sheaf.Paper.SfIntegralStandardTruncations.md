## What changed

Restored and delivered the proved module `Sheaf.Paper.SfIntegralStandardTruncations`
from its quarantine copy after the 2026-10-20 upstream cluster restore. The theorem
`WeilConjectures.sfIntegralStandardTruncations` is unchanged and has a complete proof.
The proof establishes noetherianity and finite Krull dimension, proves invertibility of
`l` on the scheme and stalks, applies the integral stratified-perfect characterization
and truncation closure, reflects boundedness along the faithful exact coefficient
restriction, and transports truncation membership using the exact-functor comparison
isomorphisms. The module's proof-only imports are the existing characterization,
uniform-complete triangulated, finite-type, and exact-functor modules recorded in its
node.

## Proved and sorry left

Closed the only hole, `WeilConjectures.sfIntegralStandardTruncations`, from node
`lem-sf-intrinsic-integral-standard-truncations`. No `sorry` remains and no new holes
were added.

## No longer needed

No imports or dependency nodes were removed. The quarantined source already uses only
the dependencies needed by the complete proof; no additional module or intermediate
statement is required.

## Where the brief, the DAG or earlier work was wrong

The earlier proof had already compiled and landed in H1, but the upstream-sync cluster
restore moved this module to quarantine. The current delivery restores that exact proved
module as the assigned rework item. No statement, definition, proof route, or consumer
requires correction.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
