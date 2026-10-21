## What changed

Restored the assigned quarantined module
`Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` from its rework archive.
Repaired the private `qcqsCostalkModel` proof: move the closed-direct-image
exactness instance after the complement identity and pass the specified open
complement and identity to `CondensedRing.closedSupport_lowerStarExact`.
Reused the existing `canonicalContinuityIsColimit` helper in
`qcqsInjectiveCostalkContinuity` instead of rebuilding the same truncated colimit
witness, avoiding a costly inference step. The optimized complete file compiled
cleanly in 44.5 seconds.
The archived public theorem, definitions, public imports and proof route remain
unchanged. Node `det-lem-constructible-ext-continuity-stratum` retains its Lean
attachment and all dependencies; proof step 4 explains the local exactness instance.
Change record: `coord/changes/A6-constructible-ext-stratum-exactness.md`.

## Proved and sorry left

This is a zero-hole repair. The archived module has 0 sorries; the restored module
has 0 sorries. Closed 0 of 0 holes; added 0 holes; split off 0 statements.
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum`
(node `det-lem-constructible-ext-continuity-stratum`) and every private helper
retain complete proofs. Imported dependencies retain their own proof obligations.

## No longer needed

None. No import, dependency, module, Lean attachment or tool approval is removed.
The archived proof generalizes the existing noetherian costalk and finite-free
Hom continuity arguments to the actual qcqs hypotheses. Reusing their general
helpers is the existing shorter route. Mathlib searches for closed-pushforward
exactness find generic adjoint colimit preservation, and the project already
specializes that result in `closedSupport_lowerStarExact`; no new lemma is needed.
No unit route is bypassed, and no global pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The module is absent from lean/ because it is quarantined, not because it was
withdrawn. Its preserved proof calls an obsolete partial interface:
`closedSupport_lowerStarExact Λ i` leaves the open-complement scheme implicit
argument unresolved. The current signature requires `Λ i k hik'` and the local
finite-colimit instance is needed for the exact left adjoint used by the derived
adjunction. The repair uses only hypotheses already present. The archived direct
consumer `Sheaf.Paper.ConstructibleExtContinuity` has an unchanged application of
the public theorem. The downstream scan reports zero live consumers; quarantine
was checked separately. A standalone parent compile cannot find the quarantined
item in the published build, so the consumer check compiles both files together
in a separate scratch directory. No source-library declaration is modified.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
