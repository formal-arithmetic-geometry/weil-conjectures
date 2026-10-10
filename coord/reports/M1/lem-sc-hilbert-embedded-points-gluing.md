# Stage-1 report

Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-embedded-points-gluing.json` — statement node, split, no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.

Attachments: none. No sorry-free project declaration states this item exactly.

WANTED: `literature/stacks-project/divisors.tex`, Tag 02OL (Lemma 31.5.8), for the affine embedded-point submodule construction and its gluing paragraph.
WANTED: `literature/stacks-project/sheaves.tex`, Tags 00AL and 04TN, for the sheaf and morphism gluing used in step 2.

The imported item had no proof and its `blueprint.from.place` was inherited from the parent rather than naming the gluing clause; I filled it with the precise induction-step gluing sentence. The item itself is not a restatement of the parent: it isolates only the compatibility, coherent-submodule, and quotient-gluing portion. No new node was needed because the DAG already contains the affine tilde comparison, sheaf-of-modules gluing, affine finite-type criterion, locally-Noetherian coherence criterion, open-restriction colimits, and affine cokernel formula.

## Review by M1

I read the item and parent proof context in the DAG, and checked the referenced project source tree for the blueprint tag and any declaration carrying `(blueprint: lem-sc-hilbert-embedded-points-gluing)`; no project declaration exists. The Stacks source files named by the imported node are not present in this checkout, so the report records them as WANTED rather than claiming to have read unavailable prose. The proof follows the imported Tag 02OL route and the already-split generic gluing result.

Step 1 uses the exact affine tilde/global-sections unit and counit statements to turn each finite section submodule into a subsheaf, together with the coherent-sheaf definition's quasi-coherence clause. The localization hypothesis is used only to identify the resulting restrictions with the prescribed smaller-affine submodules.

Step 2 uses the existing sheaf-gluing statement, which supplies a module from overlap isomorphisms satisfying the cocycle condition, and its affine tilde comparison to justify that the local inclusions are the same on overlaps. The morphism-gluing clause then gives the global inclusion into `F`.

Step 3 uses the affine tilde unit, the affine finite-type equivalence between finite sections and finite type, and the locally-Noetherian equivalence between coherent and quasi-coherent finite-type modules. The locally Noetherian hypothesis is checked against the cited definition; no stronger quasi-separated or finite-cover hypothesis is introduced.

Step 4 uses that restriction along an open immersion preserves colimits, so the global cokernel restricts to each local cokernel, and the affine cokernel statement identifying sections with `F(U_i)/N_i`. The existing gluing lemma's uniqueness clause confirms that the local quotients are the restrictions of the single quotient sheaf `F/K`.

I also ran the required Mathlib searches for the item: LeanFinder returned only general tilde/localization declarations, Loogle and the Mathlib grep returned no matching gluing theorem, and LeanSearch was unavailable; these exact searches and verdicts are recorded in the node. Small edge cases are covered: an empty finite submodule gives the zero local subsheaf, and the quotient is then the original affine section module; localization compatibility is equality on every affine refinement, so it also handles empty overlaps.

## Second reading by M1

- Statement: checked against Stacks Divisors Tag 02OL (label `lemma-remove-embedded-points`) and the parent induction clause; verdict: repaired the formerly implicit localization data into explicit finitely generated submodules on principal affine opens.
- Step 1: checked against the affine tilde/counit and unit statements and the coherent finite-type criterion; verdict: valid after restricting the localization claim to principal affine opens.
- Step 2: checked against Sheaves Tags 00AL and 04TN as represented by `lem-weil-pbc-glue-sheaves-of-modules`; verdict: valid, with both sheaf-gluing and morphism-gluing clauses cited.
- Step 3: checked against the affine finite-type criterion clause (a), its affine-cover consequence (c), and the locally Noetherian coherence equivalence; verdict: valid.
- Step 4: checked against restriction preserving colimits, the affine cokernel formula, and uniqueness of glued morphisms; verdict: valid.
- New nodes: none; the item is the only statement node and all helper facts are existing DAG nodes. Mathlib searches were rerun by the worker and recorded as LeanFinder no match, Loogle no match, grep no match, and LeanSearch unavailable.
- Changes: made the statement self-contained by naming the affine cover, section rings/modules, finitely generated submodules, principal-affine localization identifications, and overlap agreement; added the finitely generated-module definition dependency; rewrote step 1 to match that data; expanded citations for the morphism-gluing, affine-cover finite-type, and restriction-colimit clauses.
- Edge cases checked: $N_i=0$, $N_i=M_i$, an empty overlap, and a field affine; all give the expected zero, whole, restriction, and quotient constructions.
