# Stage-1 split: lem-sc-affine-rhom-qcoherent

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-affine-rhom-qcoherent.json`: split the item; no new nodes or Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every proof citation.

## Attachments

None. Searches of `WeilConjectures/` for the item tag, affine RHom, derived Hom, and Ext found no project declaration stating this item. The derived-Hom declarations found concern different sheaf categories.

## Sources and corrections

I read `perfect.tex` Lemma `lemma-quasi-coherence-internal-hom` (Tag 0A6H), especially part (3) and its finite-projective-complex proof, `algebra.tex` Lemma `lemma-resolution-by-finite-free` (Tag 00LP), `more-algebra.tex` equation `equation-h0-RHom` (Tag 0A64), and `cohomology.tex` Lemma `lemma-restriction-RHom-to-U` (Tag 08DL). This checkout lacks the regenerated Stacks `.tex` files; the same source files were available read-only at `/home/ubuntu/c1-stacks-review/`. The item's source field had listed Tag 08DL as though it gave the affine comparison; it only gives restriction to opens, so I corrected the source to Tag 0A6H. The existing proof-dependency nodes cover every substantial ingredient, so creating another node would duplicate them.

The original `mathlib_searches` records did not correspond to this worker's searches. I replaced them with the actual two phrasings run through LeanFinder, Loogle, and grep, plus the LeanSearch attempt, which returned unavailable. The hits were generic sheafification, sheaf cohomology, Ext, and derived-functor declarations; none states the affine derived internal-Hom comparison. The source proof has no assumption beyond the item's Noetherian ring and finite modules: these give a bounded-above finite-free resolution, while the second argument in degree zero is bounded below.

## Review by G1

For step 1 I checked the statement of the finite-free-resolution node: it supplies an exact resolution of a finite module over a Noetherian ring. The associated-sheaf node identifies sections on every principal open with module localization; the localization-exactness node preserves the augmented complex's exactness, and the sheaf-stalk-exactness node detects the resulting quasi-isomorphism. The free rank can be zero, which causes no exception.

For step 2 I checked that `lem-sc-derived-hom-finite-free-model` actually states that the sheaf Hom complex represents RHom for a bounded-above finite-free first complex and bounded-below second complex. Both hypotheses hold here. The remaining finite-free calculation is written out termwise: for each $A^{n_i}$, both Hom sheaves are $\\widetilde N^{n_i}$ and the differential comes from the same matrix. No citation is used for a construction found only in another node's proof.

For step 3, the tilde-stalk statement identifies each stalk with localization, the localization-exactness statement preserves kernels, images, and quotients, the cohomology-sheaf definition names the kernel/image quotient, and the stalk-exactness statement detects the sheaf isomorphism. The complex has no negative terms, including in the case $M=0$, so negative cohomology vanishes.

For step 4, the projective-resolution node identifies the ordinary module Hom complex with ring RHom in every integer degree, and the ring-RHom-cohomology node identifies its nonnegative cohomology with Ext. The associated-sheaf node explicitly says every tilde module is quasi-coherent. I checked the zero ring, $M=0$, $N=0$, and $M=A$: the formula gives zero for negative degrees, and for $M=A$ gives $\\widetilde N$ in degree zero and zero above. These cases expose no missing finiteness, boundedness, or shift hypothesis.

I searched the DAG by Tags 00LP, 0A64, 06XR, 08DL, and by affine RHom and localization wording, and searched the whole blueprint for affine derived Hom and Ext sheaves. The nodes cited above are existing statements, not new restatements of the item. I corrected the item source and search record, then checked each citation against the cited node's own statement and placed its verbatim excerpt in `citations.json`. The tool uses declared in `split_report` are generic algebra and sheaf facts from other units; they supply inputs, not a replacement for this unit's proof route.

## Unfinished

None.

## Second reading by G1

- Item statement: checked against Perfect Complexes Lemma Tag 0A6H(3), with finite modules in degree zero; hypotheses and the $q<0$/$q\ge0$ split agree, including $A$ Noetherian and $M,N$ finite.
- Step 1: checked against Algebra Tag 00LP(2), Schemes Tag 01HV(4),(5),(7), and Modules Tag 01AG(5); the finite-free resolution, localization exactness, stalk localization, and stalk criterion provide exactly the claimed quasi-isomorphism.
- Step 2: checked against Perfect Complexes Tag 0A6H(3) and Cohomology's finite-free Hom-complex calculation; the termwise $\\widetilde N^{n_i}$ identification and differential compatibility are explicit.
- Step 3: checked against Schemes Tag 01HV(7), localization exactness, Modules Tag 01AG(5), and the cohomology-sheaf definition; kernels, images, quotients, and negative-degree vanishing are used under the stated hypotheses.
- Step 4: checked against Derived Categories Tag 06XR and More on Algebra Tag 0A64; the projective-resolution comparison gives Ext in every $q\\ge0$, and the associated-sheaf node gives quasi-coherence.
- New nodes: none; all dependencies are existing nodes, and DAG/blueprint searches found no duplicate or Mathlib declaration for the affine sheaf-RHom comparison.
- Edge cases: checked $A=0$, $M=0$, $N=0$, $M=A$, and the empty affine spectrum; the complex and Ext formula have the claimed zero and degree-zero behavior.
- Changed Step 1 to cite the existing stalk-localization node and spell out localization at $A\\setminus\\mathfrak p$ before applying stalkwise exactness; added its verbatim citation quote. No statement or source was weakened.
