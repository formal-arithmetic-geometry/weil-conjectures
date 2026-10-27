## What changed

Proved `MonoidAlgebra.SplitUnitGroupIdealTensor.split_unit_group_ideal_tensor`, preserving
its full statement and all existing definitions. Ideal extension follows by writing
`z^(q,g) = z^(q,1) z^(1,g)`. The forward tensor map comes from the monomial presentation;
the inverse is the canonical tensor map induced by inclusion. Both composites and
multiplication compatibility are checked on monomial pure tensors. Coefficient change
uses semilinear tensor maps; the inverse naturality square is checked on arbitrary pure
tensors and the forward square follows from the inverse identities.

Added `Sheaf.RingTheory.MonomialIdealTensorPresentation`, proving the monomial presentation
from Mathlib's ideal-support criterion, the integer basis of the supported submodule,
and `LinearMap.liftBaseChange`. It also proves monomial balancing and additive
extensionality. No existing module besides the assigned item was changed. The new
imports in the item are proof imports; existing public imports and interfaces are unchanged.
The DAG records the same split-chart argument with the new presentation lemma explicit.

Validation: both modules compiled cleanly through `lcompile.py`: the presentation helper
in 4.7 seconds and the assigned item in 9.2 seconds, below the per-file limit. Text checks
confirm that all existing definitions, the comparison structure, and the full assigned
theorem signature are unchanged. Both files contain zero `sorry` occurrences.

## Proved and sorry left

Closed the item's single hole:
`MonoidAlgebra.SplitUnitGroupIdealTensor.split_unit_group_ideal_tensor`
(`lem-trf-split-unit-group-ideal-tensor`).

The added theorem `MonoidAlgebra.MonomialIdealTensorPresentation.exists_lift` and all
supporting declarations are proved (`lem-trf-monomial-ideal-tensor-presentation`).
Holes closed: 1. Holes added: 0. Sorries left: none. This is a proof, not a decomposition.

## No longer needed

None. No public imports were removed, and the original tensor universal-property
dependency is still used. The new presentation lemma implements the original monomial
calculation; no unit, parent, source declaration, or previously needed module is withdrawn.
No flatness, ideal-tensor injectivity, monoid cancellation, or localization dependency
is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The node's informal argument is valid,
including for the empty monoid ideal, a zero coefficient ring, noncancellative monoids,
and characters with zero values. Its monomial-span calculation needed an explicit
support/basis implementation in Lean. The original comparison signature also requires
its monomial equation for any supplied ideal elements equal to monomials; their indices
lie in K by the support criterion and closure of K.

## New nodes

`lem-trf-monomial-ideal-tensor-presentation`: monomial balancing, additive extensionality,
and extension of compatible monomial values to a coefficient-linear tensor map.
Source: the finite-monomial calculation in ILO VI 3.7(a), printed p. 75, and VIII 3.4.3,
printed p. 110, using Stacks Tag 00CX. The complete elementary proof is recorded in the
node and theorem docstring. Mathlib searches by LeanSearch, LeanFinder, Loogle and grep
found support criteria and whole-algebra tensor infrastructure but no exact ideal-tensor
presentation theorem. A blueprint search for "monomial ideal tensor" found no duplicate.
No change record is needed: existing signatures, definitions and public imports are unchanged.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
