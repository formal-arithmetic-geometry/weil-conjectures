1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-affine-section-localization.json`: item, statement, split.
- No new nodes; both dependencies are existing nodes and the Mathlib leaf `lem-weil-pbc-affine-scheme-qcqs` was read.

2. Attachments

None. A grep of the slopmaster2 source for the item id, 01PW, and the localization terminology found no sorry-free declaration stating this item exactly.

3. WANTED

None. The cited Stacks source files are represented in the repository metadata and the proof follows Properties Lemma 01PW and its affine specialization in Cohomology of Schemes Lemma 09MR.

4. What was checked and changed

The original item was unsplit with the affine statement and the correct dependencies. I searched the whole DAG and blueprint for the 01PW localization fact and found the existing general node `lem-sc-p1-invertible-section-localization`; I also found the existing Mathlib leaf `lem-weil-pbc-affine-scheme-qcqs`. I did not create duplicate nodes.

Step 1 uses exactly the affine-scheme leaf's conclusion that an affine scheme is quasi-compact and quasi-separated. I checked its source statement and its Mathlib match: `Scheme.compactSpace_of_isAffine` and `quasiSeparatedSpace_of_isAffine`, with the scheme/topological quasi-separated identification. The affine hypothesis in the item is therefore sufficient.

Step 2 uses exactly the statement of `lem-sc-p1-invertible-section-localization`: for a quasi-compact, quasi-separated scheme, an invertible module, a global section, and a quasi-coherent module, the degree-zero localization map sends a fraction to restriction tensored with the inverse section and is an isomorphism. Substituting `X=Y`, `N=H^0_*`, and the item’s `Y_s` gives the stated map. The item’s affine, invertible, section, and quasi-coherent hypotheses match the general theorem hypothesis by hypothesis; Step 1 supplies qcqs. This is declared as the off-unit tool use required by the brief.

I verified the edge cases already noted in the source context: with `\mathcal L=\mathcal O_Y` this is ordinary module localization on a principal open; with `s=0`, both the degree-zero localization and sections on the empty nonvanishing locus are zero. The exact node statements are quoted verbatim in `citations.json`.

## Review by K1

I read the item node, its blueprint ancestor reference (`lem-sc-pic-proper-ntorsion`, the 09MR affine-open p=0 clause), the existing general localization node, and the affine qcqs leaf. The Stacks source is Properties Lemma 01PW (part (2), equation `module-invert-s`) together with the affine case paragraph of Cohomology of Schemes Lemma 09MR. The item statement agrees with that specialization: affine `Y`, invertible `\mathcal L`, section `s`, quasi-coherent `\mathcal F`, the graded direct sum over all integer tensor powers, the degree-zero localization, and the fraction map are all present.

For Step 1, the cited leaf states the exact qc and qs conclusion used; no proof detail from that node was assumed beyond its statement. For Step 2, the cited general theorem states the exact localization isomorphism and fraction formula used; the only extra work is the explicit substitution `X=Y`, justified by Step 1. Both steps are non-elementary and cite their dependencies. The proof dependency union matches the step uses, and `citations.json` quotes verbatim parts of each cited statement.

The item has no new statement-only nodes, so there are no additional Mathlib searches or new-node edge cases. The existing affine leaf's recorded searches cover LeanSearch, Loogle/LeanFinder, grep, and local source verification. I corrected the item from `unsplit` to `split`, added the two source-grounded proof steps, filled `proof_deps` and `proof_origin`, and added the blueprint split report with the required tool-use declaration.

5. What could not be finished

Nothing. The delivery remains to be checked by the project scripts and pushed by the delivery tool.
