## What changed

Filled `DerivedCategory.degreeZero_abelian_criterion` in
`Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion`, preserving its signature.
The proof follows the existing seven-step DAG plan. It constructs the kernel and cokernel
isomorphisms from the exact homology sequence and their universal properties, retaining both
specified equations. Triangulated closure and cohomology closure put both objects in the
subcategory. Mathlib supplies the fully faithful restriction, concentration criterion,
short-exact-sequence triangle, split biproduct sequence, and abelian full-subcategory criterion.

Replaced the private `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` import with
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`, which provides the degree-zero
specialization of the same short-exact-sequence construction. Existing public imports stay.
Refined step 2 of the node proof to record membership transfer across the concentrated-single
isomorphism. No definitions, public interfaces, consumer modules, or DAG dependencies change.

## Proved and sorry left

Closed the single hole in `DerivedCategory.degreeZero_abelian_criterion`
(node `lem-sfb-derived-degree-zero-abelian-criterion`). Holes added: zero. Holes left: zero.
The complete module compiled cleanly through `lcompile.py` in 6.1 seconds, with no warnings.

## No longer needed

Removed the direct private import `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`:
`SingleTriangle` imports it and specializes its construction. No mathematical dependency,
node, or module is pruned; all ten planned Mathlib dependency nodes are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The proof uses the canonical ambient t-structure
only to apply the existing concentrated-single Mathlib lemma; no t-structure on the given
subcategory is assumed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
