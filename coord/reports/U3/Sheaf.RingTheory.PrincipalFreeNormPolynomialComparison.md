## What changed

Filled `Algebra.principal_free_norm_polynomial_comparison` in the assigned module,
without changing its signature. Three proved private helpers handle transitive
scalar extension, the local images of the specified chosen characteristic
polynomial (including its arbitrary test-algebra universe), and evaluation of
localized multiplication at the numerator of 1. The main proof computes the
local matrix of X−C(b), descends coefficientwise equality, applies Cayley–Hamilton,
and descends the evaluation identity. The expansion supplies monicity and degree.
Rank zero follows from the expansion and evaluation. A zero base forces a zero
algebra by unitality. Updated the assigned node's proof to match these steps.

Added proof imports for ULift rings and polynomial monicity. All existing public
imports and all existing declaration signatures are preserved. No other existing
module is changed.

Validation: the complete proof compiled remotely in 8.1 seconds. Removed the
reported unused simp arguments before delivery. The delivery tool repeats the
compile and checks the axioms of every delivered declaration.

## Proved and sorry left

Closed the sole original hole:
`Algebra.principal_free_norm_polynomial_comparison`
(`lem-a1-principal-free-norm-polynomial-comparison`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
All three private helpers are proved; no new nodes or split statements.

## No longer needed

No dependency node or module is pruned. All the stated proof dependencies are
used through their existing source declarations or Mathlib matches. No import
is removed. In rank zero the separate local empty-basis argument is unnecessary:
the already established expansion and annihilation identity give 1_B=0_B.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The specified chosen polynomial's test-ring
universe prevents directly substituting the unlifted localization when w is
arbitrary. The proved local-comparison helper uses ULift and injectivity to
respect that universe exactly. The statement and the unit route are preserved.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
