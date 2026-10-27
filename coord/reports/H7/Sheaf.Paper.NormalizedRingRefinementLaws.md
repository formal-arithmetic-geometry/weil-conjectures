## What changed

Replaced the hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_ring_refinement_laws`
with a finite coefficient proof and a case split using a fixed integral-stage theorem.
The original public statement and public import are unchanged. All added item imports
are proof imports; no other existing Lean module is changed.

At finite coefficients the proof obtains a bounded etale-origin witness from the
proved `finiteRing_constructibleDerived_origin`, applies the single-arrow coordinate
comparison in `Sheaf.Paper.FiniteRingRefinementCoordinates`, transports the proved
`FrobeniusExchange.intrinsicCompactificationCoherence` equations through the supplied
left realizations and `finiteImageIso`, and reflects them through the faithful full
inclusion. Three proved private categorical helpers perform coordinate transport,
identity and composition; explicit associativity avoids unfolding derived morphisms.

The integral case is isolated in
`Sheaf.Paper.IntegralNormalizedRingRefinementLaws`. Its statement fixes one integral
coefficient stage and asserts neither finite coefficient nor scalar-change laws.
The parent combines it with the finite proof by a complete RingStage case split.
Both new statements have nodes, sources and complete proof plans in their docstrings.

The complete three-module sandbox set compiled. The finite argument also compiled
in isolation in 16.3 seconds; the integral split statement compiled in 5 seconds.
The earlier attempted integral normalization proof is retained in scratch diagnostics,
but is not claimed as a completed proof or included in the delivery.

## Proved and sorry left

Original holes closed: 1 of 1,
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_ring_refinement_laws`
(node `lem-sf-normalized-ring-refinement-laws`). The item has no remaining `sorry`.

Holes added: 2, each with its entire proof exactly `by sorry`:

- `WeilConjectures.ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates`
  (node `lem-sf-finite-ring-refinement-coordinates`): one normalized finite refinement
  on one retained etale-origin object, asserting no identity or composition laws.
- `WeilConjectures.ConstructibleExceptionalCoefficients.integral_normalized_ring_refinement_laws`
  (node `lem-sf-integral-normalized-ring-refinement-laws`): only the completed integral
  coefficient case. Its proof specializes existing integral pasting after checking
  normalization and the uniform finite-Tor diagram domains.

This is a decomposition, with one hole closed and two added, not a net hole reduction
or an axiom-free proof claim. The finite categorical coherence combination and the
RingStage case split are complete Lean proofs.

## No longer needed

No original public import is removed and no module is withdrawn or globally pruned.
The finite route uses `lem-weil-pbc-finite-ring-constructible-derived-origin` in place
of the original direct `lem-sf-proetale-constructible-origin` dependency because it
supplies exactly the constant-ring intrinsic realization needed by witnessed coherence.
The compactification-coherence argument remains in the route through
`FrobeniusWitnessedCompactification`.

The item itself no longer imports `RingOpenRefinement`, `IntegralRingedClopenComparison`
or `IntegralNormalizedRefinementPasting`: these belong to the proof plan of the new
integral case. Their nodes remain needed there, so they are not globally pruned.
The generic open-uniqueness helper and the large integral specialization attempt are
removed from the item because the final reduction does not use them directly.

## Where the brief, the DAG or earlier work was wrong

The finite map identification is not a conclusion of compactification coherence:
the normalized ring-sheaf and witnessed constant-coefficient presentations differ.
The new coordinate theorem records the omitted comparison for one arrow, rather
than restating identity and composition under another name.

The older completed coefficient refinement API adds absolute separatedness of both
schemes and cannot be used with this item's unchanged hypotheses. The relative
`integralNormalizedRefinementPasting` API fits. An attempted explicit specialization
of it repeatedly exceeded the accepted compile time, including a version with a
small proved wrapper and an isolated normalization helper. The remaining integral
case is therefore stated explicitly with its full specialization proof plan.
No compile limit is increased, shared definition is changed, or false statement
replaced by a weaker one. The item's quarantined/rework attachment is preserved.

A broad dependency scan encountered the pre-existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`; neither node is edited.

## New nodes

`lem-sf-finite-ring-refinement-coordinates` identifies the single finite ring-sheaf
proper/open word with `FrobeniusExchange.intrinsicRefinement`. It retains the supplied
etale witness and needs no cartesian refinement square. Sources: current blueprint
compactification-coherence proof and Stacks 03D6, 03DI, 0F7B. Zero inputs, empty opens
and identity refinements follow from the same invertible-unit cancellation argument.

`lem-sf-integral-normalized-ring-refinement-laws` is the fixed completed integral
coefficient case. Its proof plan verifies realization compatibility, identifies the
normalized open comparisons, obtains all diagram domains from the uniform Tor interval,
and applies the existing relative integral pasting theorem. The parent also contains
an independently written finite proof, so this is a proper case reduction.

Mathlib searches of all three required kinds are recorded in `searches.jsonl` and
in each new node. No existing definition or statement is changed, so no change record
is needed.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
