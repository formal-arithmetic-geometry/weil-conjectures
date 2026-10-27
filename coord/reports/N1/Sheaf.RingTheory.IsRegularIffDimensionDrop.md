## What changed

Filled `RingTheory.Sequence.isRegular_iff_dimension_drop` in
`Sheaf.RingTheory.IsRegularIffDimensionDrop`. The forward implication composes
Mathlib's `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hreg` with `hd`.
The reverse implication applies the existing
`RingTheory.Sequence.isRegular_of_dimension_drop d hd hdepth xs hmem`.
The statement, definitions, docstrings and imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes: `RingTheory.Sequence.isRegular_iff_dimension_drop`
(node `lem-trf-cm-regular-sequence-generator-count`). Zero holes remain in the
item; zero holes added; zero statements split off. This proves both implications
from the existing declarations, rather than decomposing either implication.

## No longer needed

None. Both private proof imports are used:
`Mathlib.RingTheory.KrullDimension.Regular` for the forward formula and
`WeilConjectures.RingTheory.IsRegularOfDimensionDrop` for the converse. The public
imports supply the original statement's notions. All declared dependencies and
the unit route are retained; no nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement or dependency defect found. The DAG's forward step discusses
converting the additive equality to ordinary dimension subtraction. Since the
Lean statement already uses the additive equality in `WithBot ℕ∞`, that
conversion is unnecessary in Lean: transitivity with `hd` suffices. This is the
same two-direction proof route, so no node update is required.

Read the Stacks 02JN equivalence in `literature/stacks-project/algebra.tex`,
the item node, all three proof dependencies and their Lean signatures, and the
`sk-i-curve-zero` unit record and current blueprint text. Empty lists and lengths
exceeding `d` need no separate branch: both cited results quantify over every
list and use the identical additive dimension equality. No hypotheses were
added, dropped or specialized. LeanFinder and Loogle found the exact forward
Mathlib lemma; repository and Mathlib grep confirmed the existing converse and
found no shorter equivalence to apply.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
