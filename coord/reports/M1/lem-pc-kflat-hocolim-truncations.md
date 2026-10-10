1. Files written:

- `lem-pc-kflat-hocolim-truncations.json`: statement split, 3 proof steps.
- `lem-pc-complex-hocolim-colimit.json`: statement-only unsplit node; Mathlib no match.
- `lem-pc-filtered-colimit-quasi-iso.json`: statement-only unsplit node; Mathlib no match.

2. Attachments: none.

3. WANTED: `literature/stacks-project/sites-cohomology.tex`, Lemma 06YS. The source was read at `/home/ubuntu/c1-stacks-review/sites-cohomology.tex` because the repository literature checkout does not contain it.

4. The imported item had no proof. I retained its statement and split the two reusable non-elementary facts rather than restating clauses as child nodes. The hocolim child is the telescope calculation; the filtered-colimit child uses exact filtered colimits in the module category. No Lean declaration with the blueprint tag or matching statement exists in the source checkout.

## Not duplicates

`lem-pc-complex-hocolim-colimit` vs `lem-kun-complex-colimit-hocolim`: the existing node is only for etale sheaves, while the new node is for arbitrary sheaves of modules on an arbitrary site and explicitly defines the telescope.

`lem-pc-filtered-colimit-quasi-iso` vs `lem-kun-kflat-criteria`: the existing node concerns K-flatness of etale sheaf complexes, while the new node concerns preservation of quasi-isomorphisms under arbitrary filtered colimits on a ringed site.

`lem-pc-complex-hocolim-colimit` vs `lem-pc-kflat-hocolim-truncations`: the child treats an arbitrary sequence and identifies its telescope with the termwise colimit; the item specializes to good truncations and proves comparison with the original complex.
`lem-pc-complex-hocolim-colimit` vs `lem-pc-kflat-bounded-flat-replacement`: the existing node constructs bounded-above flat replacements and does not state any hocolim/colimit comparison.
`lem-pc-complex-hocolim-colimit` vs `lem-pc-kflat-resolution`: the existing node asserts existence of K-flat resolutions, using the telescope comparison but not stating it as a general lemma.
`lem-pc-complex-hocolim-colimit` vs `def-pc-kflat-complex`: the existing node defines K-flatness, with no colimit or telescope assertion.
`lem-pc-complex-hocolim-colimit` vs `lem-pc-kflat-closure`: the existing node states closure of K-flat complexes under sums and cones, not the telescope-to-colimit quasi-isomorphism.
`lem-pc-complex-hocolim-colimit` vs `lem-pur-integral-operations-well-defined`: the existing node concerns integral derived operations and only cites K-flat constructions as background.
`lem-pc-complex-hocolim-colimit` vs `lem-kun-flat-resolution-existence`: the existing node is restricted to the small etale site and packages a resolution existence theorem, not the arbitrary-site telescope calculation.
`lem-pc-complex-hocolim-colimit` vs `def-weil-integral-derived-reduction`: the existing node defines integral reduction and does not state a general hocolim comparison.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-pc-kflat-hocolim-truncations`: the child states preservation for every filtered diagram of quasi-isomorphisms; the item uses this as a separate clause alongside the truncation comparison.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-pc-kflat-bounded-flat-replacement`: the existing node gives bounded flat replacements and no filtered-colimit homology result.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-pc-kflat-resolution`: the existing node asserts existence of a K-flat resolution, not exactness of filtered colimits on quasi-isomorphisms.
`lem-pc-filtered-colimit-quasi-iso` vs `def-pc-kflat-complex`: the existing node is a definition of K-flatness and contains no filtered-colimit preservation theorem.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-pc-kflat-closure`: the existing node concerns closure under K-flat operations; it does not state that filtered colimits preserve quasi-isomorphisms.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-pur-integral-operations-well-defined`: the existing node concerns well-definedness of integral derived operations, not general filtered diagrams of complexes.
`lem-pc-filtered-colimit-quasi-iso` vs `lem-kun-flat-resolution-existence`: the existing node is an etale-site K-flat resolution theorem and does not state filtered-colimit preservation of quasi-isomorphisms.
`lem-pc-filtered-colimit-quasi-iso` vs `def-weil-integral-derived-reduction`: the existing node defines an integral reduction object and does not state the filtered-colimit quasi-isomorphism property.

## Review by M1

I read the Stacks 06YS proof in the review checkout, including the telescope construction and the sentence that the induced colimit map is a quasi-isomorphism because filtered colimits are exact. I checked the existing etale analogue and kept it as a non-duplicate because its site and coefficient hypotheses are narrower. Step 1 cites the new telescope statement, whose statement explicitly gives the comparison map and its quasi-isomorphism. Step 2 uses only the definition of good truncation and stabilization in each degree; this is marked elementary and was checked on a complex concentrated in one degree and on the zero complex. Step 3 cites the new filtered-colimit statement verbatim. That statement cites `prop-pur-kinjective-resolutions-exist` for exact filtered colimits on an arbitrary ringed site; this is declared as a generic tool use because no node in this unit supplies that category-theoretic fact. All hypotheses in both new statements introduce the site, ring sheaf, and complexes explicitly. Mathlib searches were run for each node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

5. Unfinished: the source document is not copied into this repository's literature directory, so the report records it as WANTED; no other work remains for this split.

## Second reading by M1

- Item statement: checked against Stacks Tag 06YS, including the good-truncation telescope and filtered-colimit clauses; verdict: hypotheses and conclusions retained.
- Step 1: checked against `lem-pc-complex-hocolim-colimit` statement and Tag 06YS; verdict: the hocolim comparison is cited with the required transition maps.
- Step 2: checked degreewise from the definition of good truncation and `def-pc-quasi-iso-modules`; verdict: elementary stabilization argument, including zero and one-degree complexes.
- Step 3: checked against `prop-pur-kinjective-resolutions-exist` and Tag 06YS; verdict: exact filtered colimits commute with kernels, images, and cohomology, so quasi-isomorphisms remain quasi-isomorphisms.
- `lem-pc-complex-hocolim-colimit`: self-contained arbitrary ringed-site statement, Tag 06YS, no Mathlib match; verdict: retained.
- Removed `lem-pc-filtered-colimit-quasi-iso`: it restated the item's second clause; its proof is now written directly as Step 3, using the existing exact-colimits node.
- Repaired the item proof, source place, proof dependencies, and verbatim citations; no new node remains for the restated clause.
