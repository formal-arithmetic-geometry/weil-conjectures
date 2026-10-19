## What changed

Proved `DerivedCategory.perfect_of_derivedComplete` with its signature unchanged.
For each element of the ideal, use the existing localization-tower criterion and the
Mathlib right orthogonal to the shift closure of the localized ring. This property is
triangulated; the proof supplies its retract closure explicitly. The existing
classical-generator equality and the envelope universal property then give the result.
Countable products are supplied by the existing exact-products existence theorem and
Mathlib's module AB4Star instance. Updated the proof docstring and DAG route.

## Proved and sorry left

Closed one hole: `DerivedCategory.perfect_of_derivedComplete`
(`lem-sf-perfect-over-derived-complete-ring`). Added zero holes. Zero `sorry` remain
in the delivered module. No new declarations or intermediate theorem modules.
The proof uses the existing `DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton`,
whose proof remains a separate existing hole; this delivery does not claim to close it.

## No longer needed

Removed the proof import `Sheaf.RingTheory.DerivedCompleteProductsTriangles`, and removed
`lem-weil-pbc-module-derived-complete-products-triangles` from this node's proof dependencies
and top-level tool approvals. Mathlib's triangulated right-orthogonal instances supply
the required closure directly, so the products-and-triangles theorem is unnecessary for
this proof. No claim is made that its module is globally unreachable from other parents.
The original remaining proof dependencies are retained. The new direct proof dependency
`lem-weil-derived-countable-products-existence` supplies actual Roos triangles for the ring.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original plan is valid, but its triangle-closure step is
shorter through the Mathlib orthogonal API. This changes only the route below the unit;
`sk-thm-sf-package` has no realized statement or proof-step attachment to this node.
The localization is used with `ULift.{0}`, so its module universe is precisely the ring
universe and the arbitrary derived-category universe remains unchanged. The proof uses
no regularity, nonzerodivisor or finite-generation hypotheses and also covers zero rings,
the zero ideal and the unit ideal.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
