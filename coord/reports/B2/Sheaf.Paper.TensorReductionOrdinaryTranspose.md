## What changed

Filled `WeilConjectures.tensorReduction_ordinaryTranspose` in
`Sheaf.Paper.TensorReductionOrdinaryTranspose`. The proof follows the existing
ordinary finite-transpose and full Roos coordinate argument. Proved private
helpers isolate the scalar-unit and projection calculations, both Roos coordinates,
the finite tensor coordinates, the prescribed tower component, the finite-level
calculation, and elementary categorical identities. Added proof-only imports
of `Sheaf.Paper.StrictTensorAugmentation` and
`Sheaf.Paper.IntegralAmbientOperationModels` (the latter with `import all` to use
its proved private coordinate API). Public imports and all existing signatures
are preserved. Updated the item's proof record to match these calculations.

Moved the fully proved finite generator comparison to the new module
`Sheaf.Paper.TensorReductionFiniteTransposeCoordinates`, with public theorem
`WeilConjectures.tensorReduction_finiteTransposeCoordinates`. This isolates a
self-contained calculation after local unfolding improvements, so each compilation
unit can meet the 60-second limit. It adds no unfinished proof obligation. The
item imports this module only for its proof.

Also isolated the proved ordinary finite-projection calculation in
`Sheaf.Paper.TensorReductionFiniteProjection`, with public theorem
`WeilConjectures.tensorReduction_finiteProjection`. It combines the normalized
adjunction projection with the prescribed tensor-tower components. The parent
now assembles the two finite equations and the two Roos coordinates.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.tensorReduction_ordinaryTranspose`
(node `lem-coef-tensor-reduction-ordinary-transpose`). Added zero holes; no proof obligation is split
off. Both new supporting theorems are fully proved. No `sorry` remains in any of
the three delivered modules. Existing imported proof obligations retain their
own nodes and are not claimed as closed here.

## No longer needed

None. All four original declared proof dependencies are used. No module or
public import is removed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The original proof can be formalized
using the existing scalar-unit normalization, prescribed tensor-tower components,
and both strict Roos coordinates, without another decomposition. The rework row
records a prior quarantine caused by a transitive false-tail import; the current
item source exists and has been preserved with its original Lean attachment.

## New nodes

`lem-coef-tensor-reduction-finite-transpose-coordinates` records the proved finite
adjunction-transpose coordinate calculation from step 3 of the original node.
It is a strict part of the original argument: it has no ordinary reduction/limit
transpose, tensor-tower comparison, shifted coordinate, or full Roos conclusion.
Its Lean module is `Sheaf.Paper.TensorReductionFiniteTransposeCoordinates`.
No definition or statement change record is needed.

`lem-coef-tensor-reduction-finite-projection` records the proved calculation of the
ordinary transpose at one finite tensor level, corresponding to the original
node's first two steps. It has a single finite normalization hypothesis and a
single finite projection as conclusion; it proves no strict augmentation or full
Roos identity. Its module is `Sheaf.Paper.TensorReductionFiniteProjection`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
