## What changed

Proved `WeilConjectures.PurScalarProjection.diagram_projection` from the existing
`ordinaryCompletedSquare`, with its statement unchanged. Added the proved private
helper `scalarTensorCompleted_unit`, obtained directly from
`scalarCompletion_existsUnique` and naturality of the completion unit.
Moved `diagram_projection` after `projection_unit` so that its proof can use both
completion-unit equations. No imports, definitions, public signatures or other
modules changed.

The proof first obtains constructibility of the scalar-extended inputs from
`ordinaryCompletedSquare`. The existing pullback and tensor domain lemmas give
constructibility of their ordinary inner tensor and invertibility of its actual
completion unit. `finiteTor_of_constructible` supplies the required finite-Tor
witness. Precomposing the completed square with the scalar-extended source unit,
the proper/open projection-unit equations, scalar completion normalization and
unit naturality give equality of the ordinary routes followed by compact support
of the inner unit. Cancel that invertible map, then apply the whole native
reduction functor and postcompose with `nativeRealization`.

The node's proof records this shorter assembly. The unit route is retained.

Validation: the item compiled cleanly through `lcompile.py` in 57.3 seconds,
with no errors or warnings. All 31 existing declaration headers, all existing
docstrings and all imports were checked against the shared source and preserved.

## Proved and sorry left

Closed 1 of the 8 original holes:
`WeilConjectures.PurScalarProjection.diagram_projection`.
Added 0 holes; split off 0 statements.

The following 7 existing holes remain unchanged, all attached to
`lem-pur-compact-support-scalar-projection-identification`:

- `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`
- `WeilConjectures.PurScalarProjection.properProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.openProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`
- `WeilConjectures.PurScalarProjection.ordinaryCompletedSquare`

The new proof uses existing named theorem dependencies that still contain
`sorry`; it does not establish the final theorem without those dependencies.

## No longer needed

No imports, nodes or modules can be removed by this delivery. In particular,
the ringed exchange/tensor and open normalization dependencies remain needed
for the remaining `ordinaryCompletedSquare` and `native_scalar_identification`
proofs. `diagram_projection` does not need an independent representative-level
or finite-evaluation argument: it follows from the existing completed square
and the actual invertible completion units on these constructible inputs.

## Where the brief, the DAG or earlier work was wrong

The DAG's direct ringed-diagram proof of `diagram_projection` duplicates work
already contained in `ordinaryCompletedSquare`. The integral equality of the
two ordinary routes can be recovered from that square before applying the
native reduction functor. This changes the proof route only, not its statement.
No faithfulness of reduction or evaluation functors is used. The cancellation
is justified by the tensor domain theorem for the actual F inner completion
unit; it makes no claim about arbitrary ambient input units.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
