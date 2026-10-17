## What changed

Proved `AlgebraicGeometry.exists_fibre_dimension_bound` in
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`, with its signature unchanged.
The proof follows Stacks 0A3V/02FZ and the declared dependencies: finite local fibre
dimensions, affine openness, a finite open subcover, and the supremum formula.
Finiteness is obtained by applying `exists_topologicalKrullDim_le` directly to each
whole fibre, which is quasi-compact and locally of finite type over its residue field.
The repair removes the three top-level duplicate declarations rejected by the
landing checker (`dimensionAt_inducing_le`, `dimensionAt_homeomorph`, and
`fibre_dimension_source_open_immersion`). Their local-dimension arguments are
now carried out in the needed proofs, while the finite maximum still handles an
empty source and the supremum formula handles empty fibres.
Updated the existing node's proof, proof dependencies and proof origin, removed
obsolete tool uses, and aligned the theorem's proof docstring with the implementation.

Validation: the complete item compiled through `lcompile.py` with no errors or
warnings in 4.0 seconds after import pruning and namespace qualification. The statement retains its original
universe and all three instance hypotheses. Lean Finder, Loogle and Mathlib grep
found no existing uniform fibre-dimension theorem; the proof uses the existing
field-scheme finiteness and affine openness declarations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_fibre_dimension_bound`
(node `lem-fin-finite-type-fibre-dimension-bound`).

Holes added: 0. Holes remaining in the delivered module: 0. Split off: 0.
This is a proof from existing declared dependencies, including the algebraic
openness theorem, whose transitive dependencies remain independent project items;
no claim is made that their remaining holes have been closed by this delivery.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.Mathlib.Topology.KrullDimension`: already publicly available
  through the retained imports; its local-dimension definition and open-subspace
  theorem are still used.
- `Sheaf.Topology.DimensionSupremumLocalDimensions`: retired re-export; use
  `WeilConjectures.Topology.DimensionSupremumLocalDimensions` directly.
- `Mathlib.AlgebraicGeometry.Pullbacks`: the pullback API is already available
  through the retained imports.
- `Mathlib.AlgebraicGeometry.Restrict`: the restriction API is already available
  through the retained imports.
- `Mathlib.AlgebraicGeometry.AffineScheme`: affine charts and `isoSpec` are already
  available through the retained imports.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: no quasi-separatedness
  argument is needed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the pullback API is
  already available through the retained imports.

Removed these direct node dependencies and their tool uses:

- `lem-weil-pbc-fibre-product-affine-spectra`: no separate affine fibre construction
  is needed for finiteness; the retained affine coordinate comparison provides
  the coordinate identification needed for openness.
- `lem-weil-pbc-open-preimage-fibre-product`: the proof uses base change of an open
  immersion and the fibre homeomorphism directly, rather than this particular
  restriction-square statement.
- `lem-weil-pbc-affine-scheme-qcqs`: finiteness is applied to the whole fibre, whose
  quasi-compactness follows from the assumed quasi-compactness of f. No affine
  quasi-separatedness is used.

These are removals of direct dependencies, not a claim that every corresponding
module has disappeared from the transitive target closure. No module is withdrawn,
and no unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The original DAG's affine construction
for local finiteness was unnecessary under the existing quasi-compactness
hypothesis: each whole fibre satisfies the already declared field-scheme theorem.
The increasing sequence of dimension loci can be replaced by one bounded open
neighbourhood at each point and the maximum over a finite subcover. These changes
preserve the cited Stacks proof and the target statement.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
