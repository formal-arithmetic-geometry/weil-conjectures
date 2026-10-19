## Files written

- `dag/nodes/sec-trace-formula/lem-trf-constructible-etale-finite-affine-syzygy.json` — item, statement split; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement excerpts for every cited node in each proof step.

## Attachments

None. I searched the slopmaster2 source and found no declaration carrying this item or its exact finite-syzygy statement.

## WANTED

None. The cited Stacks source is present locally.

## Not duplicates

- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constructible-module-finite-zero-cokernel`: the existing node gives one finite affine epimorphism for one constructible sheaf; this item iterates kernels and states an exact sequence of arbitrary prescribed finite length with all syzygies constructible.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-trf-constructible-free-etale-resolution`: that node concerns bounded-above resolutions of complexes on Noetherian schemes and does not state this finite-stage syzygy construction for an arbitrary qcqs scheme.

## What was wrong or corrected

The imported item was mathematically sound, but its proof was empty and its `blueprint.from.place` was only a generic placeholder for the Ext-continuity input. I filled that place with the finite affine-free syzygy resolution used by the Ext-continuity route. I did not change the statement or dependencies. The notation `P_U` in the existing 095N node is identified with `j_{U!}\\Lambda_U` by the existing definition of etale extension by zero, so no duplicate definition node is needed.

## What I could not finish

Nothing remains unfinished at the stage-1 natural-language level.

## Review by Q52

I read the item node, its chapter `sec-trace-formula`, its unit `sk-i-curve-zero`, and the source passages in `literature/stacks-project/etale-cohomology.tex`: Tag 095N (the finite affine presentation), Tag 03RZ (constructible modules closed under kernels), and Tag 03S8 (constructibility of affine-etale extension by zero). I also read the full statements of `lem-weil-pbc-constructible-module-finite-zero-cokernel`, `def-weil-pbc-etale-sum-extension`, `def-weil-pbc-etale-sheaves`, and `thm-constructible-serre`.

Step 1 uses exactly what those statements provide: 095N supplies finitely many affine etale objects and a map with zero cokernel; the extension-by-zero definition identifies each sheafification `P_U` with `j_{U!}Λ_U`; the sheaf category is abelian; and 03RZ supplies constructibility of the newly defined kernel. The hypotheses are preserved at every induction stage: X and Λ are fixed, and K_a is constructible by the preceding induction step. Step 2 uses only abelian-category kernel exactness and finite splicing, which is an elementary verification of consecutive composites, images, and kernels; it produces the displayed exact sequence and retains constructibility from Step 1.

I checked the two small boundary cases: for r=1 the chain is the single short exact sequence `0→K_1→E_0→F→0`; for F=0 the 095N epimorphism may be the empty finite family and every kernel is zero, so the construction still works. I searched the whole DAG and blueprint for 095N, 03RZ, 03S8, and the finite affine-free/syzygy wording; the two nearest existing nodes differ as recorded above. The required LeanFinder, Loogle, grep, and LeanSearch commands were run for the item and recorded in `searches.jsonl`; they returned only generic Mathlib sheaf/projective-resolution results, so the item is not a Mathlib leaf.
