## What changed

Proved `AlgebraicGeometry.Scheme.openSheafCoproduct_baseChange` in
`Sheaf.AlgebraicGeometry.OpenSheafCoproductBaseChange`. All existing public
signatures, definitions and public imports are unchanged. Added the private proof
import `Mathlib.CategoryTheory.Sites.SubcanonicalOver` and proved private helpers.

The proof follows the node's partition argument. It first derives a small support
for an arbitrary given scheme coproduct, transports the geometry of the canonical
small coproduct, and proves sheaf descent on the summands. The existing
`fppfSheaf_coproduct_partition` gives the comparison section and cartesian summand
squares. Its partition of any test section gives existence and uniqueness of a
lift, hence the pullback comparison. Coproduct maps give test-change compatibility;
pullback pasting and Yoneda reflection give the asserted scheme pullback.
The node's proof and proof origin now record these implementation details.

Final single-file server compilation succeeded without warnings in 21.3 seconds.
All Lean lines are at most 100 characters.

Validated against Stacks, Spaces, Tag 02WR, `lemma-glueing-algebraic-spaces`, first
proof paragraph, and the current blueprint unit. The proof treats empty indices,
empty summands, arbitrary index universes, repeated opens and non-covering opens.
The unit route is unchanged. The explicit chosen test data already supply the
local open representatives, so the preserved `hmono` and `hopen` binders are
redundant in this proof; only their unused-variable warnings are disabled locally.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.openSheafCoproduct_baseChange`
(node `lem-trf-open-sheaf-coproduct-base-change`).

No `sorry` remains in the item. No holes added; no statements split off.
The proof uses the existing, separately assigned
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition`
(node `lem-trf-fppf-sheaf-coproduct-partition`), whose proof is still `sorry` in the
shared library. This delivery closes the assigned hole from that stated dependency;
it does not claim that the dependency's axioms are already eliminated.

## No longer needed

None. No imports removed and no nodes or modules withdrawn. The partition theorem
and the planned scheme coproduct, open immersion and fppf descent facts are used.
The direct Mathlib subcanonical instance packages the planned descent argument.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was necessary. The DAG's small-index scheme
coproduct facts require a support reduction for the actual universe-polymorphic
statement; this is proved privately from the given coproduct universal property,
without imposing an additional smallness hypothesis.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
