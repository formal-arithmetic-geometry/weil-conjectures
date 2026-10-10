1. Files written:

   - `lem-pc-complex-hocolim-colimit.json`: statement node, split proof, no Mathlib leaf.
   - No new nodes; existing `lem-weil-pbc-complex-ses-triangle` is reused.

2. Attachments: none.

3. WANTED: `literature/stacks-project/sites-cohomology.tex`, Lemma 06YS (the local literature checkout contains only the citation index, not the source text).

4. The item had no Lean declaration with the blueprint tag or an exact sorry-free statement. I checked the imported analogue `lem-kun-complex-colimit-hocolim`; it is restricted to etale sheaves, while this item quantifies over arbitrary sheaves of modules on a ringed site, so it is recorded as `same_as` but cannot replace the item. The proof follows the telescope argument of Stacks 06YS: injectivity of `1-shift`, identification of its cokernel with the termwise filtered colimit, and the distinguished triangle supplied by `lem-weil-pbc-complex-ses-triangle`. I read the cited node and verified that it states the short-exact-complex triangle used in step 2; the quasi-isomorphism notion is exactly the statement of `def-pc-quasi-iso-modules`. Small cases checked: a constant sequence has `1-shift` cokernel equal to one copy of the complex, and a sequence starting with zero gives the expected first-stage colimit. Mathlib searches were run for LeanFinder, Loogle, grep, and LeanSearch; no exact telescope theorem was found and LeanSearch was unavailable.

5. What remains unfinished: no source text is available locally for a line-by-line literature check; the exact Stacks tag and argument are recorded so the second reader can verify them when reviewing.

## Review by G1

I read the target node, the Picard chapter and unit records, the related imported etale telescope node, and the existing short-exact-complex triangle node. Step 1 uses only the cochain-complex notion and spells out the finite-support induction proving injectivity plus the degreewise cokernel/filtered-colimit identification. Step 2 uses the cited triangle statement verbatim for a degreewise short exact sequence and invokes the cited quasi-isomorphism definition for the conclusion. I verified that all hypotheses of the triangle node are met in the abelian category of sheaves of O-modules, and that the statement's arbitrary ringed-site scope is strictly broader than the etale-only analogue. I corrected the initial empty proof by adding these two complete steps, recording the existing analogue as `same_as`, and preserving the source's telescope construction and hypotheses.

## Second reading by G1

- Item statement: checked against Derived Categories Lemma 0949 (label `derived-lemma-colim-hocolim`) and the definitions of cochain complexes and quasi-isomorphisms; hypotheses and conclusion agree.
- Step 1: checked against the cochain-complex definition and the direct-sum/shift construction in Lemma 0949; finite-support injectivity and the degreewise cokernel computation are elementary and correctly stated.
- Step 2: checked against the short-exact-complex triangle node and Lemma 0949; the cone-to-cokernel map and its contractible kernel are now written explicitly, so the quasi-isomorphism conclusion is supported.
- Existing cited nodes: their statements were opened and each citation quote in `citations.json` is verbatim; no new nodes are present.
- Small cases: zero complexes, a constant system, and a system beginning with zero give the expected zero, one-copy, and first-stage colimits.

Changes: corrected the source from the unrelated tag 06YS to tag 0949, corrected the creation-item metadata, and replaced the unsupported “standard cone-to-cokernel comparison” phrase with its explicit map and contracting homotopy.

## Source error

The worker cited tag 06YS, but the Stacks tag index identifies 06YS as the K-flat resolution lemma. The telescope statement and proof are Derived Categories Lemma 0949 (`derived-lemma-colim-hocolim`); the node and proof citations were corrected accordingly.
