## What changed

Proved `AlgebraicGeometry.Etale.ordinaryFiniteP1_twisted_unit_baseChange`
with its original statement. The proof derives the sheaf transport composition law
from transport uniqueness and the existing finite-twist pullback laws. Generic
lemmas pass this law through the degree-zero embedding and shift 2. The exact
derived square, mate-unit identity, and naturality of the unit then give the
asserted equality after cancelling the exact/left-derived comparisons.

Proof imports provide transport uniqueness, single-functor composition, shift
compatibility, derived mates, and the derived-adjunction normalization. No public
import changes. A local additive-instance priority aligns the inherited additive
structures of the generic and concrete categories.

The complete proof initially exceeded 60 seconds during kernel conversion.
`OrdinaryFiniteP1Kummer` now names the canonical single-degree functor before
applying its object map. `OrdinaryFiniteP1Arrows` names the canonical exact and
left-derived comparisons using that functor. These are explicit constructions,
definitionally the old objects and arrows. Existing signatures and attributes are
unchanged. `EvenLineProductIntegrationMaps` uses that object interface in its private
ordinary-line constructibility helper and applies the site-comparison theorem
for a generic coefficient ring before specializing. Local irreducibility keeps
the constructed line objects abstract during elaboration. A private proof import
provides the Kummer interface directly. All three modules are unclaimed.
The definition change and its users are recorded in
`coord/changes/A2-finite-p1-cached-degree-zero.md`; the existing definition nodes
attach the new API and explain this factorization. Target meanings reopen for
review, with no mathematical change.

Each modified module passes its per-file compile check. The original
`P1KummerTraceSiteTransport`, `GeoP1Cohomology`, and
`OrdinaryFiniteP1KummerMaps` consumers compile against the factored definitions
without adaptations (34.7, 47.6, and 9.2 seconds respectively in the final
consumer checks). Profiling code is removed from the packet.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.ordinaryFiniteP1_twisted_unit_baseChange`,
node `lem-sp-finite-p1-twisted-unit-base-change`: one of one original holes.
Added holes: none. Remaining holes in delivered Lean files: none. Split off: none.
All private helpers and the public equation `ordinaryFiniteSingleFunctor_eq` are
proved. This proof uses the already stated finite-twist pullback theorem as
intended by stage 3; it does not claim that dependency has been proved without
sorry.

## No longer needed

None. No original imports, nodes, modules, or declarations are removed.
All five original proof dependencies remain used: ordinary arrows, exact
exchange, transport uniqueness, finite-twist pullback, and the mate-unit identity.
The degree-zero calculation also uses the existing ordinary Kummer definition
node. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The original plan works over arbitrary bases without
a Noetherian hypothesis, exchange invertibility, or a projective-line splitting.
The previously unnamed canonical single-degree functor and comparisons caused
expensive kernel conversions; their definitionally identical named interfaces
resolve that performance issue. The consumer's generic constructibility interface now uses the same degree-zero
object before specialization, as documented in the change record.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
