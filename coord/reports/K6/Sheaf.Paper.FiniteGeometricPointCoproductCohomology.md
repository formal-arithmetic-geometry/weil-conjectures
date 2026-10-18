## What changed

Proved `AlgebraicGeometry.finite_geometric_point_coproduct_cohomology` with its existing
signature and visibility unchanged. Positive-degree vanishing follows from the declared
single-point calculation and finite-coproduct assembly, using the existing comparison
between Ext cohomology and derived global sections. The canonical degree-zero map is
factored through sections on the disjoint open summands and their strictly henselian
canonical germs. The proof treats the empty coproduct without a nonemptiness assumption.
All added imports are proof-only. The copied DAG node records this route.

Validation: the complete module is checked with the project server compiler and the
stage-3 delivery dry run. No definition, public import, or statement was changed.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.finite_geometric_point_coproduct_cohomology`
(node `lem-weil-pbc-finite-geometric-point-coproduct-cohomology`).
Added 0 holes; split off 0 statements. No `sorry` remains in any delivered Lean file.
The imported single-point theorem remains an existing dependency; its proof is not
part of this delivery.

## No longer needed

Removed the proof-only import `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
and the corresponding node `lem-weil-pbc-inverse-image-stalk-germ` from this proof's
DAG dependencies and obsolete tool-use list. The degree-zero argument works directly
with germs of the original sheaf on each open image, so no inverse-image stalk
identification is needed. The point-cohomology and coproduct-assembly imports remain
necessary for positive degrees. No other original import or declared dependency was
removed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The finite-coproduct assembly uses Ext-based `Sheaf.H`, whereas the assigned statement
and point theorem use homology of derived global sections. Existing proved comparison
lemmas bridge these APIs; no new comparison obligation is required.

The point theorem's degree-zero clause supplies an unspecified natural isomorphism,
which alone does not identify the particular canonical germ in the assigned statement.
The strictly henselian open-germ theorem and disjoint-cover theorem prove invertibility
of that exact germ map directly. The unit record `sk-prop-cd` has no realized nodes
requiring the discarded inverse-image-stalk route. No statement or definition repair
was necessary.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
