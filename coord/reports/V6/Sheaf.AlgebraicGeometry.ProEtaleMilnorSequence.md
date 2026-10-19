## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.milnor_sequence` without changing its
signature. Exact countable products give the explicit natural Roos cohomology
sequence. Specializing it to towers concentrated in degree zero gives the
natural degree-zero and degree-one isomorphisms and vanishing in other degrees.
Transport along the degree-one isomorphism gives the final short exact sequence
with the same inclusion and projection.

The retained work constructs the pointwise short exact sequence and proves
its naturality theorem: compare the existing
strict Roos map with the shifted mapping-cone map, construct its triangle map,
prove naturality of the boundary, and cancel cokernel projections or test limit
coordinates to obtain the two endpoint squares.

Moved the four unchanged tower definitions into `MilnorTower`, publicly imported
by the original module, to avoid a cycle between the generic calculation and its
specialization. Added three generic calculation modules, all proved. See
`coord/changes/V6-milnor-tower-location.md` for the unchanged interface and users.
Every delivered module was compiled through lcompile.py; final delivery preflight
also checks the declarations and their axioms. The resumed session retained all
proofs, checked the current sources and direct consumers, and reran the previously
missing LeanSearch query recorded in all four new nodes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.ProEt.milnor_sequence` (det-pe-milnor-sequence).
Original module: 1 of 1 holes closed, 0 left. Holes added: 0.

Also proved every newly introduced theorem, including
`AlgebraicGeometry.Scheme.ProEt.milnor_shortExact`
(lem-pe-roos-pointwise-exact),
`AlgebraicGeometry.Scheme.ProEt.roos_cohomology_naturality`
(lem-pe-roos-cohomology-naturality), and
`AlgebraicGeometry.Scheme.ProEt.roos_cohomology_sequence`
(lem-pe-roos-cohomology-sequence). No delivered declaration contains `sorry`.
The existing imported exact-products theorem is now proved in the current sources;
this delivery does not modify that dependency.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
and dependency det-pe-products-derived: the generic homology functor preserves
exact products by the existing DegreewiseLimits API, so the stronger assertion
that termwise products represent derived-category products is unnecessary.
The original public import `Sheaf.Paper.IntegralOperationsWellDefined` stays:
its actual Roos construction and maps are used. Removed the direct proof import
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` from the item module;
RoosCohomologyMaps imports it publicly for its boundary construction.
No other declared dependencies are pruned: the long exact sequence, products,
abelian-category operations, derived category and inverse limits occur in the
explicit generic calculation. The unit's cone and product-cohomology route stays.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly described the new naturality theorem as an
existing imported hole and said that no new modules or nodes were introduced.
This report accounts for the whole retained sandbox. Naturality is now proved.
Corrected the new nodes’ blueprint ancestry records and added explicit references to
the definition nodes used by their statements. No mathematical statement is disputed
or weakened.

## New nodes

`def-pe-milnor-towers` records the unchanged tower definitions in MilnorTower.

`lem-pe-roos-pointwise-exact` records the explicit boundary and projection,
product/cohomology comparisons, kernel-to-limit comparison and proved short
exactness in RoosCohomologyMaps.

`lem-pe-roos-cohomology-naturality` records the proved two squares for the
explicit maps in RoosCohomologyNaturality. The proof uses the existing strict
Roos map, not an arbitrary map completing a distinguished triangle.

`lem-pe-roos-cohomology-sequence` packages those explicit maps, their proved
short exactness and naturality in RoosCohomologySequence.

Change record: `coord/changes/V6-milnor-tower-location.md`.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
