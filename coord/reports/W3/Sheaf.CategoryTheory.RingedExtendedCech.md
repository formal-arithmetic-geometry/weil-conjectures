## What changed

Filled all four proof holes in `Sheaf.CategoryTheory.RingedExtendedCech`.
The graded-term evaluations simplify their defining conditionals. The differential-square
identity splits on whether the source degree is zero: at zero the next differential
vanishes, and elsewhere the first differential vanishes. The augmentation compatibility
uses `HomologicalComplex.single_obj_d` and the relation `m = n + 1`, then splits on
`n = 0`: in that case the degree-one augmentation vanishes; otherwise the source
differential vanishes, using `CochainComplex.of_d`.

Every declaration signature, definition, docstring and import is unchanged. The existing
construction and proof route of `def-weil-pbc-ringed-extended-cech` are preserved, so no
node update is needed. Read the extended alternating complex construction and the global
extended Cech lemma in `literature/stacks-project/algebraization.tex`.

Validation: the complete module compiled through `lcompile.py` in 8.8 seconds with exit
code zero and no warnings. LeanFinder, Loogle, Mathlib source and both library roots were
searched; Loogle located the single-complex zero-differential lemma used in the proof.

## Proved and sorry left

Closed four of four original holes, all attached to node
`def-weil-pbc-ringed-extended-cech`:

- `CategoryTheory.ringedLocalizationTwoTermX_zero`.
- `CategoryTheory.ringedLocalizationTwoTermX_one`.
- `CategoryTheory.ringedLocalizationTwoTermD_comp`.
- `CategoryTheory.ringedLocalizationTwoTermAugmentationF_comm`.

No sorry remains in the item module. No holes were added or split off. Existing holes
in imported localization theory are outside this item and were not changed.

## No longer needed

None. All three existing public imports are needed by the unchanged definitions:
`Sheaf.CategoryTheory.RingedSectionLocalization` supplies the localization and its map,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` supplies the additive closed tensor
structure, and `Mathlib.Algebra.Homology.Monoidal` supplies tensor complexes and their
morphisms. No declared dependency, node or module is bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The assigned node has no numbered proof steps;
the four existing theorem docstrings give the elementary degreewise verifications, which
are now implemented directly in Lean. No definition repair or consumer adaptation was
necessary.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
