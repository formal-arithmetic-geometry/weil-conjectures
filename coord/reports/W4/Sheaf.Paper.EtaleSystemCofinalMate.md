## What changed

Filled the continuity, coefficient-ring identification, exactness, ramification
monotonicity, coefficient-map naturality, and local-field specialization proofs
in `Sheaf.Paper.EtaleSystemCofinalMate`. All existing declaration signatures,
definitions, visibility, and imports are preserved. Added only proved private
helpers for the reconstructed coefficient functor, general sequence-site
pushforward exactness, and quotient-tower maps.

Continuity specializes the existing monotone sequence-site reindexing theorem.
Exactness uses the forgetful functors that reflect finite limits and colimits;
cocontinuity makes reindexing on abelian sheaves preserve colimits. Coefficient
naturality is functoriality on the thin index category. The local-field proof
identifies the entire quotient towers by their maps on representatives and
constructs the two coefficient objects explicitly from the existing finite-stage
theorem for the identity field extension. No quotient-ring data is chosen from
an unproved existence statement.

## Proved and sorry left

Closed six of the original seven holes, all in the namespace
`AlgebraicGeometry.Etale.SystemProjection`:

- `cofinalSite_continuous`.
- `cofinalRing`.
- `cofinalRestriction_exact`.
- `cofinalRamification_strictMono`.
- `cofinalCoefficient_naturality`.
- `etaleSystemCofinalMate_localField`.

One original hole remains: `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCofinalMate`,
node `lem-pur-etale-system-cofinal-mate`. Its original statement, source, complete
proof docstring, and DAG plan are retained. The outstanding work is the
construction of the normalized `CofinalSupport` package and its composition
coherence, followed by the formal right-adjoint mate identities. In particular,
the existing selected-extension theory uses the strict-system presentation,
whereas the package also needs its representative-normalized transport to the
sequence-site presentation. The six completed proofs do not assume this
remaining theorem.

Holes added: none. Holes split off: none. This is a partial proof delivery,
not a decomposition of the remaining theorem.

## No longer needed

No modules or DAG nodes are withdrawn. No imports are removed: the original
main theorem and its unfinished geometric argument still require the recorded
proof dependencies. The completed local-field specialization itself only uses
ideal powers, quotient maps, and `Padic.local_field_coefficient_stages`; it does
not require the compact-support comparison or a new scalar-adjunction argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The rework row is historical:
the current item source is present in `lean/`, and this delivery preserves its
Lean attachment and dependencies rather than withdrawing its quarantine archive.
The existing block-repetition module already proves continuity for arbitrary
monotone reindexings, including the increasing embeddings used here.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
