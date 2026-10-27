## What changed

Filled `AlgebraicTopology.AugmentedPosetChains.BooleanCoatom.excision_homology`
without changing its statement. Added the private, explicitly constructed
`reversalHomologyIso`, using Mathlib's `restrictionHomologyIso` to handle the
integer grading reversal. The proof uses the last clause of `BooleanCoatom.excision`,
applies derived homology in degree `-n`, then composes the localization,
shift, and reversal homology identifications. Added the private proof import
`Mathlib.Algebra.Homology.Embedding.RestrictionHomology`. Updated the item's
node to record these standard identifications. No shared definitions or other
modules changed. The final module compiled cleanly with `lcompile.py` in 2.3 seconds.

## Proved and sorry left

Closed 1 hole: `AlgebraicTopology.AugmentedPosetChains.BooleanCoatom.excision_homology`
(node `lem-sfb-boolean-coatom-excision-homology`). Added 0 holes; 0 holes remain
in the item. The proof still uses the stated derived excision theorem, whose
unproved dependencies are outside this delivery; this is a proof from the
assigned declared dependency, not a claim that the entire dependency closure
is sorry-free.

## No longer needed

None. All existing statement imports and the derived-form dependency are retained.
No declared DAG dependency, node, or module is pruned. Both proof imports supply
APIs used by the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. Mathlib already supplies the generic shift and
reversal homology identifications, so the planned explicit kernel/image sign
calculation requires no new lemma or hole. The derived-form route and the unit
route are unchanged. The construction works for all integer degrees without
positivity assumptions or a separate degree-zero case.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
