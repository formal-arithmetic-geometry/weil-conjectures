## What changed

Replaced the large representative construction in `tensor_representatives` by a real
combination proof: a split existence-and-properties theorem supplies normalization,
K-flat invertibility, and the unit, while the item proves uniqueness by faithful
whiskering along the fixed section equivalence. The existing uncurrying helpers remain
because later pullback comparisons use them. The target signature is unchanged.

## Proved and sorry left

The uniqueness and assembly proof of
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.tensor_representatives` is proved.
Three strictly simpler proof obligations were split into
`Sheaf.Paper.SectionTensorRepresentativeExistence`:
`section_tensor_representative_exists_norm`, `section_tensor_representative_isIso`,
and `section_tensor_representative_unit`. These have `sorry` proofs with their
source and proof plan documented in the module. Holes closed: 1. Holes added: 3.

## No longer needed

The direct construction route in the original item proof is no longer duplicated in
this module. Its planned dependencies are carried by the split existence item; the
parent itself needs only that item and the existing section equivalence. No source
library declarations are removed.

## Where the brief, the DAG or earlier work was wrong

The parent proof can be reduced to the existence, invertibility, and unit clauses plus
faithfulness; the previous DAG proof text incorrectly required the parent to construct
all those clauses inline. The public target statement and the normalization predicate
are unchanged.

## New nodes

Added `lem-pd-section-tensor-representatives-exists`, realized by
`Sheaf.Paper.SectionTensorRepresentativeExistence`, with the three strictly simpler
statements listed above.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
