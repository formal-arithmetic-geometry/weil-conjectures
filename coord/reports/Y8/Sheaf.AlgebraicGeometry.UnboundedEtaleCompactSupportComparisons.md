## What changed

Proved `unboundedEtaleCompactSupport_open_beta` by definitional equality of the two
inverse-conjugate constructions. Proved
`unboundedEtaleCompactSupport_exchange_normalization` by transporting the canonical
inverse-image/direct-image adjunction mates, then cancelling the exact-functor
comparison isomorphisms in the compactification exchange formula. Proved `unboundedEtaleCompactSupport_tower_adjunct` by descending the sheaf open-unit
identity and cancelling the two inverse mates. Seven proved private helpers record
transport of mates, their behavior under whiskering, and the inverse-mate unit equation.
Proved `unboundedEtaleCompactSupport_baseChange_id` from invertibility and the
successive-base-change equation: an invertible idempotent is the identity. The proof
uses a local irreducibility attribute to avoid unfolding the exchange during conversion.
Added proof-only imports of `UpperLowerStarAdjunctionCompat`,
`MapDerivedCategoryMate`, and `UpperLowerStar.Coherence`. Existing statements, definitions and public imports are unchanged.
The required change record is `coord/changes/unbounded-etale-compact-support-proof-elaboration.md`; its local attribute has no downstream effect.

## Proved and sorry left

Closed 4 of the original 15 holes:

- `unboundedEtaleCompactSupport_open_beta`.
- `unboundedEtaleCompactSupport_exchange_normalization`.
- `unboundedEtaleCompactSupport_tower_adjunct`.
- `unboundedEtaleCompactSupport_baseChange_id`.

Added no holes and split off no statements. The 11 unchanged holes below all realize
`lem-amb-unbounded-compact-support-comparisons`:

- `unboundedEtaleCompactSupport_comparison_coherence`.
- `unboundedEtaleCompactSupport_refinement_normalization`.
- `unboundedEtaleLowerShriekCompIso_tower`.
- `unboundedEtaleLowerShriekCompIso_assoc`.
- `unboundedEtaleLowerShriekCompIso_units`.
- `unboundedEtaleCompactSupport_baseChange`.
- `unboundedEtaleCompactSupport_baseChange_comp`.
- `unboundedEtaleCompactSupport_baseChange_composition`.
- `unboundedEtaleCompactSupport_comparison_plus`.
- `unboundedEtaleCompactSupport_composition_plus`.
- `unboundedEtaleCompactSupport_exchange_plus`.

## No longer needed

No modules or imports are globally pruned in this partial delivery: the remaining
comparison, tower, pasting and bounded-below obligations still use their planned route.
The beta equality itself needs no auxiliary theorem: both sides reduce to the same
inverse conjugate. The exchange normalization needs neither a new K-injective
representative argument nor proper base change, finite-coefficient vanishing, or the
proper/open interchange theorem; it is an equality of canonical mates and the existing
transport isomorphisms. Those dependencies remain relevant to the unproved clauses.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The exchange-normalization proof can be completed
formally using the existing equality identifying the two derived adjunctions. Its
localization and representative arguments are already contained in that equality and
the functor-composition comparison API.

The identity proof uses the existing pasting and invertibility statements in this
module; both remain open and are listed above. Its local irreducibility setting
changes only proof elaboration, not the definition or any exported signature.
The existing node
`dag/nodes/sec-smooth-purity/lem-amb-unbounded-compact-support-comparisons.json`
now records this identity subargument in step 10. No new nodes are introduced.

The previous attempt completed compilation and axiom probes but timed out during
preflight before pushing. This continuation retained all four proofs, checked the
diff against current sources, and resumed the required delivery validation.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
