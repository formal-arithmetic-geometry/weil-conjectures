## What changed

Proved `AlgebraicGeometry.ProEtale.affineEtale_largeLimit_factorization` in
`Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitFactorization`, preserving its entire
signature and public imports. Its proof privately imports the existing
`Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitEquality` theorem.

The proof forms the full category of actual projected stages inside the
structured-arrow category of affine etale objects under the limit. This category
is essentially small in universe u. Cofilteredness uses the existing eventual
equality theorem only to equalize the additional parallel arrows. The given
limit property transfers to this diagram by an explicit universal-property
proof. After taking its small model, Mathlib's existing finite-presentation
factorization theorem applies. Cone naturality then transports its stage map
back to an original stage. Updated the item's DAG proof and proof dependencies
to this route. No other existing module, declaration, or node is changed.
The final module compiled remotely in 3.5 seconds with no warnings or errors;
its theorem signature and public imports match the original. The import-cycle
check permits the new private dependency.

## Proved and sorry left

Closed one of one local holes:
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_factorization`
(node `lem-pe-affine-etale-large-limit-factorization`). There are zero local
`sorry`s left and zero new holes or split-off statements.

The proof uses the existing, still admitted declaration
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_eventualEquality`
(node `lem-pe-affine-etale-large-limit-equality`); its module is unchanged.
This is a proof from an existing dependency, not a claim that the entire
transitive dependency closure is sorry-free.

## No longer needed

No original imports were removed and no modules are withdrawn or globally
pruned. Temporary explicit imports of `Mathlib.CategoryTheory.Limits.Final` and
`Mathlib.CategoryTheory.Comma.StructuredArrow.Small` were removed because the
needed API is already available.

The planned direct dependency
`lem-weil-pbc-locally-finite-type-limit-map-equality` is replaced by the existing
larger-index equality node. The small-index equality result remains an indirect
dependency of that node; it is not globally pruned. The direct finite affine
cover, generators-and-relations, and overlap-gluing reconstruction is unnecessary
in this module: Mathlib supplies it after the size reduction. All unit-level
statements and routes are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan cited the small-index Mathlib factorization theorem in a
larger-index argument without a usable Lean universe bridge. Merely observing
that only finitely many generators and relations occur does not let that
Mathlib declaration elaborate with I in universe u+1. The proof supplies the
bridge explicitly using essential smallness of affine etale objects and the
existing eventual-equality theorem. It does not assume that I itself has a small
coinitial subcategory.

No statement is disputed or changed. Cofilteredness supplies the only required
nonempty index; neither stages nor the limit are assumed nonempty. Empty
schemes therefore remain covered. The item is below the unit's own statement
and its realized steps, so this reduction does not bypass the unit route.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
