## What changed

Filled the proof of `CategoryTheory.Adjunction.shiftedCupAdjunctionTranspose` in
`Sheaf.CategoryTheory.ShiftedCupAdjunctionTranspose`. The monoid object is the actual
Mathlib construction `F.monObjObj (𝟙_ D)`. Mathlib supplies the monoidal unit/counit
instances and the tensor/unit counit normalizations. For degree zero, apply injectivity
of the inverse adjunction equivalence and simplify the zero-shift comparisons. For the
ordered cup formula, expand the inverse transpose, use counit naturality and oplax tensor
naturality, identify each transposed factor by the adjunction inverse law, and apply `hr`.
No symmetry or degree restrictions enter the calculation.

All existing signatures, definitions, docstrings, and public imports are preserved.
The existing DAG proof and all five Mathlib dependency nodes describe this proof route.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Adjunction.shiftedCupAdjunctionTranspose`
(node `lem-sfb-shifted-cup-adjunction-transpose`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
No split statements or new definitions were added.

## No longer needed

None. No imports were added or removed. All five existing proof dependencies remain
used through their Mathlib implementations: monoidal adjunction mates, monoidal
unit/counit, tensor-unit monoid, monoid transport, and the adjunction Hom equivalence.
No nodes or modules are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

None. The complete argument follows the stated plan using existing Mathlib declarations.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
