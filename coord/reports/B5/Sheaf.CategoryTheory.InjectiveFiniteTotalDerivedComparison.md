## What changed

Filled `CategoryTheory.injective_finite_total_derived_comparison` in
`Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison`, preserving all existing
public declarations and signatures. Private helpers construct the additive finite-total
comparison from the canonical finite-coproduct comparison, prove its summand normalization,
naturality and uniqueness, transfer columnwise quasi-isomorphisms using signed transposition,
and establish injectivity and K-injectivity of the extended total and columns.

The arbitrary-resolution derived unit is transported through extension and localization.
Its inverse gives the normalized total and column comparisons; cancellation proves uniqueness.
Triple reassociation matches every triple summand in both directions, with differential
`delta + (-1)^n d_q + (-1)^(n+q) d_s`. The left comparison is conjugated by these reassociations;
its summand normalization and comparison square are proved explicitly.

Updated the node proof and dependencies to reflect the direct Mathlib K-injectivity API
and the unit-invertibility API in the recorded right-derived-functor module.

## Proved and sorry left

Closed: `CategoryTheory.injective_finite_total_derived_comparison` (one original hole).
Added: none. Split off: none. No `sorry` remains in any delivered Lean declaration.
The proof uses existing library declarations and adds no dependency statements.

## No longer needed

Proof imports `Sheaf.CategoryTheory.KInjectiveComputes` and
`Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization` are removed.
Their nodes `lem-sp-kinjective-computes` and
`lem-sfb-additive-derived-plus-unit-normalization` are unnecessary for this proof: the
bounded-below instance is already in Mathlib (clause (2) of the existing Mathlib leaf
`lem-weil-pbc-dplus-injective-representative`), and the recorded unbounded derived unit is
already invertible on K-injective complexes. Removed these two obsolete top-level
tool-use approvals; their historical split-review records are preserved.
The separate enough-injectives dependency is unnecessary: the existing Grothendieck
K-injective resolution construction supplies the precise resolution datum directly.
No declaration or module is withdrawn. All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's proposed packaged K-injective computation
and plus-derived normalization results were stronger than the clauses needed here.
The finite coproduct diagonal is explicitly finite, and degree zero is included;
extension by zero treats negative degrees. Reassociation uses the actual strict
cosimplicial operators and both internal differentials, with no exactness or preservation
of injective objects assumed of the additive functor.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
