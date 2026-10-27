## What changed

Proved `Algebra.CotangentResolution.derived_diagonal_cotangent_vanishing` with its
signature and `derivedDiagonalMultiplication` definition unchanged. The proof follows
the node's two steps, using `isIso_cotangentBaseChange` and
`localization_cotangent_vanishing` as stated.

Four proved private helpers supply the comparison calculations. The first derives the
representative transpose formula from the derived unit normalization and exact restriction
comparison. The second extends the given projective resolution to nonpositive cochain
degrees, proves it K-flat using its projective terms, and identifies the ordinary transpose
with the specified derived diagonal multiplication. Passing through the homotopy quotient
and the single-complex comparison gives exactly `derivedSquareMultiplication` for the square
with left side `f` and right side the identity. The other helpers transport cotangent
vanishing along a ring-arrow isomorphism, using the coherence identity and composition
formulas, and apply this to localization at the bottom submonoid `{1}`.

The main proof applies cotangent base change to that square and reflects the resulting
zero object through extension along the identity. Restriction along the identity is an
equivalence, so its left adjoint is an equivalence and is faithful. All added imports and
the local additive instance are for proof elaboration; public imports are preserved.

## Proved and sorry left

Closed the one original hole:
`Algebra.CotangentResolution.derived_diagonal_cotangent_vanishing`
(node `lem-trf-derived-diagonal-cotangent-vanishing`).

Added zero holes. No `sorry` remains in the delivered module. The proof uses the existing
stated base-change and localization-vanishing theorems; their proofs are separate items.
The four private helpers are proved completely. This is one hole closed, with no split-off
statements or new nodes.

## No longer needed

None of the planned dependencies is pruned. Both original proof imports remain necessary.
The proof keeps the base-change and identity-localization route; no nodes or modules are
withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The two canonical multiplication maps use different
representatives, so their identification requires the normalized derived adjunction,
the K-flat counit, extension-of-complexes comparisons, and the single-complex comparison.
These are proved in the private helpers, without altering either public definition.

Searches through LeanFinder, Loogle and Mathlib grep returned formal-etaleness and
presentation-level cotangent results, not a theorem about this full cotangent complex.
The source-library search found the generic derived-adjunction and extension comparison
lemmas used in the proof. No shorter existing cotangent-vanishing theorem was found.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
