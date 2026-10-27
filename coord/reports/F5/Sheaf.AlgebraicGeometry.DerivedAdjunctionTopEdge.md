## What changed

Reduced AlgebraicGeometry.derivedAdjunction_topEdge by an upper-truncation counit
argument. Define P = tau_{<=q} Rg_*K and transpose its inclusion i:P -> Rg_*K. The
explicit edge is inverse H^q(i) followed by the ordinary transpose on top cohomology.
Every arbitrary derived adjunct out of C<=q factors through i. Naturality of the proved
pullback top-cohomology comparison and both adjunctions gives the desired equality.
The sheafification Hom bijection and faithfulness of forgetting modules prove uniqueness.
Two generic private helpers prove the transpose/naturality calculation and sheafification
cancellation completely.

Move the nine existing local-model definitions verbatim to DerivedAdjunctionTopEdgeData,
publicly re-exported by the original module. This lets the separate local calculation
refer to the exact original terms without an import cycle. No existing statement changes.
No source-library declaration is edited. Change record:
coord/changes/F5-top-edge-data-and-truncated-counit.md.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.derivedAdjunction_topEdge
(lem-weil-pbc-derived-adjunction-top-edge) by a complete assembly proof from the new
local calculation and existing proved declarations. Added one hole:
AlgebraicGeometry.topEdgeTruncatedCounit_localClass
(lem-weil-pbc-truncated-counit-local-class), the sectionwise local-class formula for
the explicitly constructed truncated counit. This is a decomposition, not a net proof:
one original hole closed, one strictly smaller local-calculation hole added, net zero.
The item has zero remaining holes; the whole delivery has exactly one. All definitions
are actual constructions without sorry. In particular, the new lemma asserts no
arbitrary-source adjunction compatibility and no existence or uniqueness of an edge.

The new local assertion was checked on identity morphisms, arbitrary integer q,
zero source/coefficients, empty opens and nonflat morphisms. Its proof in words is the
old plan specialized to the single fixed counit, followed by cancellation of H^q(i).
The old lower-bound hypothesis on K stays verbatim in the item, although neither the
assembly nor this local calculation needs it.

Validation so far: all three delivered modules compiled; the item was compiled again
without warnings after replacing three proof-local letI declarations by have. The
moved definition block and the original theorem signature/docstring are byte-identical.
DerivedSquareLocalClasses compiled unchanged against the overlay in 19.8 seconds.

## No longer needed

Removed the original private imports:
- WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology
- WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
- Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
- Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
- Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
- WeilConjectures.AlgebraicGeometry.DerivedAdjoint
- Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose

The original five public imports remain public through the new data module. The
assembly uses upper truncation directly and does not use sequential homotopy colimits,
so def-kun-truncations and Sheaf.CategoryTheory.TruncationsAndHomotopyColimits are
unnecessary for this item. The local-calculation node likewise uses the standard
truncation interface rather than sequential homotopy colimits. No module is withdrawn.

The parent no longer directly cites these proof dependencies:

- lem-pc-ringed-space-sheafification-cohomology
- lem-pc-canonical-single-direct-image-comparison
- def-pc-ringed-spaces-derived-direct-image
- def-weil-abstract-derived-category
- def-kun-truncations
- lem-pc-derived-tstructure-orthogonality
- lem-weil-pbc-hom-out-of-triangle-exact
- lem-weil-pbc-hom-into-triangle-exact
- lem-weil-pbc-derived-single-fully-faithful
- lem-pc-pinned-pullback-counit-shifts
- lem-pc-canonical-single-adjunction-transpose
- lem-pc-pinned-derived-adjunction-shifts
- lem-pc-ringed-spaces-derived-adjoint

Except def-kun-truncations, these arguments are retained by the local-calculation
node or the unchanged data interface. This relocates dependencies and does not claim
whole-library pruning. The maintainer tool approvals removed from the parent are:

- lem-pc-ringed-space-sheafification-cohomology
- lem-pc-canonical-single-direct-image-comparison
- def-pc-ringed-spaces-derived-direct-image
- lem-pc-pinned-pullback-counit-shifts
- lem-pc-canonical-single-adjunction-transpose
- lem-pc-pinned-derived-adjunction-shifts
- lem-pc-ringed-spaces-derived-adjoint

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned truncation argument is valid, but a second
upper truncation of Rg_*K makes the arbitrary-source part a direct naturality argument.
The difficult local normalization is now isolated with its exact source and proof in
words. The original node called Hom factorization steps elementary despite their
substantial use of t-structure machinery; existing upstream Hom/cohomology tools supply
that machinery. No changed target or human unit route is required.

## New nodes

- def-weil-pbc-truncated-counit-edge: the explicit edge from the transpose of the
  upper-truncation inclusion, together with the original local-model interface.
  Module Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdgeData. Real data only.
- lem-weil-pbc-truncated-counit-local-class: its sectionwise local-class formula.
  Module Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdgeLocalCalculation. One sorry.
  Source: Stacks cohomology Tags 079W, 0BKJ, 0D5X; derived Tags 08J5 and 06XS.
  LeanSearch, LeanFinder, Loogle and source grep found only ordinary adjunctions,
  general derived units/counits and truncations; no existing normalized equation.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
