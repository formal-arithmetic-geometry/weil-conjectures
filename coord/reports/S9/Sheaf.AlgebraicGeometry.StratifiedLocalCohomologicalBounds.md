## What changed

Proved `AlgebraicGeometry.Scheme.exists_global_bounds_of_stratified_local_bounds`
in `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds`, preserving its
statement and all endpoint-attainment and empty-family clauses.

Mathlib's `QuasiCompactCover.exists_isAffineOpen_of_isCompact` supplies the finite
affine selection on each compact stratum. Both the selected opens and their
original covering members form pro-etale covers: the former is a finite cover by
quasi-compact morphisms, and the latter inherits quasi-compact covering along the
refinement morphism. This allows the local hypotheses to be used directly on the
original members. Apply exact-functor cohomology comparison, place each cohomology
module in degree zero, and use the already proved derived stratum-cover detection
theorem. Finite minimum and maximum witnesses give exactly the requested endpoints.

Added private proof imports of the existing exact-functor comparison module,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, and `Mathlib.Data.Finset.Max`.
Retained the public homology import required by the unchanged signature.
Updated the existing DAG node's proof, proof dependencies and proof origin to this
argument; removed the unused geometric-inverse-image tool approval. No definition,
statement, consumer, or upstream source declaration changes. The public import
removal is recorded in `coord/changes/S9-stratified-local-bounds-imports.md`.

The final file compiled without warnings through `lcompile.py` in 8.5 seconds
after import pruning; delivery validation and axiom checks are performed by
`deliver3.py`. Searches through leanfinder, loogle, the registered grep service,
and both source trees found the Mathlib finite-refinement API and no duplicate
of the full statement. The empty scheme, empty strata, repeated labels, infinite
original covers, and unbounded complexes are all covered by the proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.exists_global_bounds_of_stratified_local_bounds`
(node `lem-sfb-stratified-local-cohomological-bounds`).

Holes added: 0. Holes left in the item: 0. No split-off statements or modules.
This is a complete proof from existing declarations, not a decomposition.

## No longer needed

Removed imports:

- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`.

Removed direct proof dependencies:

- `lem-trf-geometric-inverse-image-exact`: the existing actual-ring exactness and
  derived comparison API suffices; its unused top-level tool approval is removed.
- `def-weil-pbc-ringed-derived-restriction`: no slice restriction or coefficient
  comparison is used by the proof.
- `def-weil-pbc-sites-and-cohomology`: finite-cover membership and refinement are
  supplied by Mathlib's pro-etale precoverage API, without covering composition.
- `def-weil-proetale-inverse-image`: the actual-ring derived inverse-image API is
  the direct dependency, and no additional inverse-image composition theorem is used.
- `lem-sc-affine-noetherian-underlying-space`: the existing `IsNoetherian`
  topological instance handles this bridge directly.

These are removals from this proof, not claims that these nodes are globally
unused; statement dependencies and other consumers remain intact. The finite
stratification and the existing stratum-detection module remain essential.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original proof plan is valid but
requires unnecessary composition of inverse images on the selected opens. The
selected original members also form a pro-etale cover, so their given bounds can
be used directly. The detection interface requires `Stratification`, while the
item uses `FiniteLocallyClosedStratification`; `Stratification.ofNoetherianSpace`
bridges them because locally closed subsets of a Noetherian space are constructible.
No change to the unit's route is involved.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
