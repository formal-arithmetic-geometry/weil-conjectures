1. Files written:

- item `pqf-lem-coherent-ft-locnoeth`: two implication steps, status `split`; no new nodes.

2. Attachments: none.

3. WANTED: `literature/stacks-project/coherent.tex`, Cohomology of Schemes Lemma 01XZ, for `pqf-lem-coherent-ft-locnoeth` (the source was read in the available `/home/ubuntu/c1-stacks-review/coherent.tex` checkout).

4. The imported proof put both directions in one paragraph and cited only definitions. I separated the directions, made the affine finite-relation localization argument explicit, and cited the existing affine tilde/global-sections, affine finite-type, Noetherian finite-presentation, finite-presentation kernel, and quasi-coherent-kernel nodes. I found no duplicate node for the 01XZ equivalence and no exact sorry-free declaration stating the item. The mandatory item searches were run: LeanSearch unavailable, LeanFinder only general Noetherian results, Loogle no coherent predicate, and Mathlib grep no exact equivalence.

5. What I could not finish: no Lean is written at stage 1. The Stacks source is not present under this repository's `literature/` tree, so the report records it as WANTED while identifying the local copy used for review.

## Review by M1

I read the item, `pqf-def-coherent`, `pqf-def-locnoeth`, and the imported 01XZ proof text. The repository does not contain `literature/stacks-project/coherent.tex`, so the report records it as WANTED; the split follows the supplied blueprint proof. Step 1 uses the coherence and locally Noetherian definitions exactly for finite generators, finite relation kernels, and Noetherian affine charts; it then uses the existing affine tilde/global-sections statement for the localization identity. Step 2 uses the existing affine finite-type criterion to obtain a finite module on each affine chart, the Noetherian finite-module finite-presentation statement, and the finite-presentation-kernel finite-type and quasi-coherent-kernel statements to verify every kernel in the definition. I opened each cited node and recorded verbatim quotes in `citations.json`; the quotes match the cited statements. I checked the empty scheme and zero module as small cases. No source or item statement was changed.

## Second reading by M1

- Item statement: checked against Stacks Tag 01XZ (label `coherent-lemma-coherent-Noetherian`) and the local copy of `coherent.tex`; the locally Noetherian, coherent, quasi-coherent, and finite-type hypotheses and conclusion agree, including the empty scheme and zero module cases.
- Step 1: checked against `pqf-def-coherent`, `pqf-def-locnoeth`, and `lem-weil-pbc-affine-tilde-gamma-adjunction`; the finite-relation localization argument is stated explicitly and the counit is used only after the principal-open section calculation.
- Step 2: checked against `pqf-def-coherent`, `pqf-def-locnoeth`, `def-weil-pbc-noetherian-ring`, `lem-weil-pbc-quasi-coherent-finite-type-affine`, and `lem-weil-pbc-quasi-coherent-module-kernel`; on each affine chart the kernel is a submodule of a finite free module, and the finite-generation induction on the rank is written in the step.
- New nodes: none; the DAG was searched for the affine finite-type, affine tilde, quasi-coherent-kernel, and Noetherian facts, and no duplicate or Mathlib declaration of the item was found.
- Small cases: the empty scheme makes both predicates vacuous; the zero module has the zero presentation and zero kernels; over a field the kernel of a finite-dimensional linear map is finite-dimensional.

Changes made: repaired the reverse step's invalid use of the surjection-only finite-presentation kernel lemma; removed the unnecessary finite-presentation and surjection-kernel dependencies; added the Noetherian-ring definition citation and its verbatim quote; retained the source as WANTED because this repository lacks `coherent.tex`.
