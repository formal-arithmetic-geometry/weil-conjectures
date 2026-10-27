## What changed

Proved `WeilConjectures.PointSystemTransport.evaluation_existsUnique` in
`Sheaf.Paper.PointSystemTransportDescent`. Its ordinary evaluation construction is
fully proved for an arbitrary point automorphism in the new module
`Sheaf.Paper.PointSystemEvaluationComparisons`, then specialized to the Frobenius
power. This separates the ordinary construction from derived transport so that
both modules can satisfy the per-file compilation limit.

The source comparison factors through completed scalar restriction. The completed
projection sends each integral constant section to its finite quotient section.
The target comparison uses the prescribed inverse coefficient map and Mathlib's
pushforward composition and congruence isomorphisms. Both are identity on sections;
module and natural-isomorphism extensionality prove uniqueness.

Optimized the existing proofs of `pull_exact`, `finiteRSections_exact`, and
`finiteSigma_existsUnique`: reduce the inverse functor explicitly, use exactness
of underlying module short complexes for scalar restriction, and use a generic
chain-map extensionality lemma. Existing public signatures, definitions, docstrings
and public imports are preserved. Added imports are private to the proofs.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.PointSystemTransport.evaluation_existsUnique`.

Two original holes remain, with their original sources and complete proof docstrings:

- `WeilConjectures.PointSystemTransport.tensorTransition_existsUnique`.
- `WeilConjectures.PointSystemTransport.finite_evaluation`.

Both belong to node `lem-trf-point-system-transport-descent`. No holes were added
or split off. The new arbitrary-automorphism evaluation theorem is fully proved;
its module contains zero holes. No previously proved declaration became a hole.

## No longer needed

None. The existing imports and declared dependencies are retained for the remaining
tensor-transition and derived finite-evaluation clauses. No modules or nodes are
withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. Direct identity-map constructions and implicit
conversions expand large module structures. Existing pushforward isomorphisms,
explicit associators, and exactness via underlying functions avoid these conversions.
The ordinary evaluation construction is compiled separately after these improvements.

## New nodes

`lem-trf-point-system-ordinary-evaluation-comparisons`, realized by the new module
`Sheaf.Paper.PointSystemEvaluationComparisons`, proves the ordinary evaluation clause
for arbitrary point automorphisms. Its proof constructs the two comparisons and
proves identity normalization and uniqueness. It introduces no unproved statement.
The parent uses its specialization to the prescribed Frobenius power. Edge cases
include the identity automorphism, zero modules, and arbitrary system transitions.
No change record is needed: existing interfaces and definitions are unchanged.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
