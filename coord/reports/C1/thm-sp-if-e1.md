1. Files written

- `dag/nodes/sec-abelian-varieties/thm-sp-if-e1.json`: split; no new child nodes; Mathlib searches found no matching declaration.
- `citations.json`: verbatim quotes for every node used by each proof step.

2. Attachments

None.

3. WANTED

None. The proof is recorded as agent-written from the blueprint proof and its Stacks reference (Tag 0130); no additional literature file was needed.

4. Review findings

The target node and the unit/chapter records were read first. I searched the whole Lean source for the blueprint id and for Cartan--Eilenberg and hypercohomology declarations; there is no sorry-free project declaration stating this theorem. The existing DAG nodes `def-sp-injective-resolutions`, `thm-sp-spectral-object-yields`, `def-sp-kinjective-bridge`, `lem-sp-kinjective-computes`, and `def-sp-left-exact-additive` were opened and their statements checked against every citation. The imported proof's first step uses the definition of an injective resolution for the row cohomology and the spectral-object theorem for the bounded second-degree filtration, its graded pieces, differential, and abutment. The second step uses the K-injective bridge to interpret `Rv` on complexes, part (2) of `lem-sp-kinjective-computes` for the bounded-below injective total complex, part (1) for resolution independence, and additivity of `v` for commuting with the finite direct sums in each total degree. The bounded-below hypothesis and nonnegative resolution degrees give the finiteness and boundedness hypotheses used in the totalization argument. I removed `thm-sp-double-complex-spectral-sequences` from `proof_deps` because neither proof step cites it; no new lemma is required. The blueprint metadata now has `same_as: []` and the node is marked `split`.

5. Unfinished work

None.

## Review by C1

I checked the source path in the item (`literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/thm-sp-if-e1.md`) and the external Stacks Tag 0130 reference recorded there. I also read the statements of all five cited nodes rather than relying on their names. Step 1 takes exactly the injective-resolution cohomology identification and the existence, `E_1`, differential, and convergence clauses of `thm-sp-spectral-object-yields`; its filtration is bounded in each total degree because the complex is bounded below and each row starts in nonnegative resolution degree. Step 2 takes the definition of `Rv` on complexes from `def-sp-kinjective-bridge`, the K-injectivity and canonical resolution-independence clauses from `lem-sp-kinjective-computes`, and finite-product preservation from `def-sp-left-exact-additive`; these are the hypotheses needed for the finite total direct sums and the displayed identification with `RvK`. Every such use has a verbatim entry in `citations.json`. I tested the dependency split for duplicate and elementary nodes: all remaining arguments are short consequences of the cited statements and the total-complex definitions, so no child node was created. Mathlib searches were run with LeanFinder, Loogle, and source grep; LeanSearch was unavailable as reported by the search tool.
## Second reading by C1

- Item statement: checked the E1 indexing, second-degree filtration, differential, and derived-functor abutment against the Cartan--Eilenberg source in `derived.tex` (Definition 015H and Lemma 015I context); removed non-source historical prose.
- Step 1: checked row resolutions and boundedness against the self-contained Cartan--Eilenberg hypotheses in the item, `def-sp-injective-resolutions`, and `thm-sp-spectral-object-yields`.
- Step 2: checked finite total-degree sums, K-injectivity, augmentation, additivity, and resolution independence against the self-contained resolution hypotheses, `lem-sp-kinjective-computes`, `def-sp-kinjective-bridge`, and `def-sp-left-exact-additive`.
- New nodes: none; duplicate and Mathlib searches were rechecked, so there are zero new nodes and zero Mathlib leaves.
- Changed the statement to remove historical dependency commentary. The imported blueprint node retains `blueprint.from: null`; no cross-unit tool node was added.
