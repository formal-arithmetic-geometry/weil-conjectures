## What changed

Replaced the saved three-part decomposition with a direct proof of
`AlgebraicGeometry.ProEtale.RationalP1.localizingPreservationChecks`. The four existing
structures and the theorem signature remain unchanged. The proof verifies the projective-line,
self-product, diagonal, complement and residue-field geometry; transports existing pullback and
proper-image preservation through the equality of the Dctf and Dbc localizing closures; and
uses Mathlib's inherited triangulated full-subcategory lift for exact restrictions.

Added `Sheaf.Paper.RationalP1PositiveLineConstructible`, containing the proved positive-line
generator theorem. Its proof uses the existing compatible-root cover, the slice/internal
module comparison, Cartesian normalization, finite free scalar models and the degree-zero
single-complex constructibility lemma. Tensor closure and the native derived tensor-shift
comparison give exact positive twists; composition gives the final twisted pullback.

Only the item, this new module and their node files change. All imports added to the item are private.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.RationalP1.localizingPreservationChecks`
(node `lem-sfb-rational-p1-localizing-preservation`).

The new theorem
`AlgebraicGeometry.ProEtale.RationalP1.positiveLine_boundedConstructible`
(node `lem-sfb-rational-p1-positive-line-constructible`) is also proved.
There are zero `sorry`s in the delivered Lean modules, zero holes added and zero split-off
unproved statements. Existing preservation dependencies are used as the stage-3 brief permits.

## No longer needed

Removed the original direct proof imports `Sheaf.Paper.CartesianCoefficients` and
`Sheaf.Paper.ProjectionMateExact`. Cartesian normalization is already supplied by the existing
pullback and local-freeness interfaces. The exactness argument uses the native derived tensor
and transports its triangulated structure across the tensor-shift isomorphism, so it does
not need the ringed projection-mate theorem
`lem-weil-pbc-ringed-projection-mate-exact`. No library module is withdrawn: those APIs may
remain transitively needed by other declarations.

The saved, never-landed `RationalP1Subclaims` module and its three proposed nodes
`lem-sfb-rational-p1-geometry-checks`, `lem-sfb-rational-p1-object-checks` and
`lem-sfb-rational-p1-functor-checks` are unnecessary. Their work is retained only in the local
scratchpad, outside the delivery. The unit's projective-line argument is retained.

## Where the brief, the DAG or earlier work was wrong

The saved packet duplicated all four structures in a privately imported subclaims module,
so the item redeclared existing names and could not compile. It also grouped three holes
in one new module, lacked complete source proofs in two docstrings, and did not update the
item's dependency route. These defects are replaced by direct proofs and a single proved
helper module. The mathematical statement and the unit route require no correction.

## New nodes

`lem-sfb-rational-p1-positive-line-constructible` records only the positive-line generator
argument (original proof step 6), for either actual rational coefficient on a qcqs scheme
where ell is invertible. It is strictly one part of the original assertion and is proved
from the existing common-root cover and finite-model machinery. There is no new definition
and no change record is needed because existing interfaces are unchanged.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
