## What changed

Filled `AlgebraicGeometry.exists_sharp_fs_orthant_embedding` in
`Sheaf.TraceFormula.SharpFsOrthantEmbedding` from the two existing declared cone results.
A proved private helper identifies the finite cone hull with nonnegative rational sums.
The coordinate homomorphism is injective because a vector in its kernel and its negative
both lie in the cone; pointedness and injective rationalization then kill that vector.
The cone's lattice-intersection description gives the required equality of sets.
The original theorem signature, definitions, and public imports are unchanged.
The node records this direct version of its third step.
Validation: the remote single-file compiler accepts the completed proof without warnings;
the delivery tool also checks compilation and declaration axioms.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_sharp_fs_orthant_embedding`
(node `lem-trf-sharp-fs-orthant-embedding`).
No holes remain in the item; no holes were added or split off.
The private helper `hull_range_eq_nonneg_sum` is proved.
The two imported existing results remain independent proof obligations of their own modules.
The construction allows `Fin 0`; empty sums and vacuous inequalities cover rank zero.

## No longer needed

No original imports, modules, or dependency nodes are removed: both declared proof
dependencies are used. The separate argument that spanning dual forms separate points
is unnecessary: the cone's no-line property proves injectivity directly.
The affine-monoid embedding found by library search does not supply the orthant
intersection property, so it is not imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The finite cone hull is a submodule
over `{q : ℚ // 0 ≤ q}`, while the dual-forms statement uses `NNRat`; the private helper
performs this coefficient conversion explicitly. Multiplicative/additive type tags
and the underlying set of the cone are normalized explicitly at their interfaces.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
