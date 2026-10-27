## What changed

Filled the three existing proof bodies in
`Sheaf.AlgebraicGeometry.DthFittingSmoothLocus`, preserving every public signature,
instance attribute, definition and public import. Added private proof imports of
`RelativeDifferentialSheafBaseChange` and `GeometricPureFibrePointDimension`.

The finite-type and quasi-coherence wrappers select the corresponding clauses of
`Scheme.Hom.relativeDifferentialSheaf_baseChange`, with identity base change.
The main proof follows the node's existing four-step route. It transports the
standard-algebraic-closure purity hypothesis to the arbitrary closures expected
by the existing geometric fibre-dimension lemma, using Spec of an algebra
equivalence, pullback pasting, and a proved private lemma transporting component
dimensions through a scheme isomorphism. It then combines the Fitting-stalk
criterion with the flat stalk map and the smoothness criterion. A proved private
padding lemma converts any spanning family of size n <= d into a Fin d family.
The first-Fitting identification uses its unique affine characterization.

Updated the item's node proof text to describe those interface conversions and
the uniqueness argument; the statement and proof-dependency set are unchanged.

## Proved and sorry left

Closed all three original holes, by declaration name:

- `AlgebraicGeometry.relativeDifferentials_isFiniteType`.
- `AlgebraicGeometry.relativeDifferentials_isQuasicoherent`.
- `AlgebraicGeometry.dthFitting_smoothLocus`.

All belong to `lem-trf-dth-fitting-smooth-locus`. Zero holes remain in the item;
zero holes were added or split off. The existing imported named theorems
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialSheaf_baseChange`,
`AlgebraicGeometry.geometric_pure_fibre_point_dimension`,
`AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally`, and
`AlgebraicGeometry.Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators`
retain their own existing holes and nodes. These are the intended stated proof
dependencies; this delivery does not claim their proofs or an axiom-free closure.
Both new private helper lemmas are completely proved.

## No longer needed

Removed the direct private imports
`WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension` and
`WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension`.
Their nodes, `lem-weil-pbc-dimension-at-point-field-extension` and
`lem-sbc-equidimensional-open-local-dimension`, are no longer direct tool uses
of this item, so their two obsolete tool_uses entries were removed. Their work
remains needed inside the geometric fibre-dimension lemma; no upstream
declaration or module is withdrawn and no global pruning is claimed.
All six existing proof dependencies are used. All existing public imports are
preserved. The trial `Mathlib.Data.Fin.Embedding` import was removed: the required
`Fin.castLE_injective` is already publicly available through
FittingIdealGenerateLocally -> PresentationFittingIdeal -> Matrix.Determinant.Basic
-> Matrix.Notation -> Fin.VecNotation -> Fin.Tuple.Basic -> Fin.Rev -> Fin.SuccPred.
No new nodes or change records are needed.

## Where the brief, the DAG or earlier work was wrong

The current DAG route is usable. The existing Lean docstring predates its
geometric fibre-dimension split, so its affine-chart Step 2 is now supplied by
the existing `geometric_pure_fibre_point_dimension` declaration rather than
reproved here. That declaration quantifies purity over every algebraic closure
and uses an iterated pullback, whereas this item's unchanged signature uses the
standard closure and the direct pullback. The proof explicitly supplies those
conversions; no hypothesis is added. The smoothness criterion returns a family
of size bounded by dimension, while the Fitting criterion uses exactly d
indices, hence the explicit zero padding. Finally, firstFittingIdealSheaf is a
uniquely characterized choice, so its comparison is proved by uniqueness rather
than definitional equality. Empty schemes/fibres and d = 0 cause no exception:
the transport is an isomorphism, all pointwise claims are vacuous when empty,
and padding works for the empty Fin 0 family.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
