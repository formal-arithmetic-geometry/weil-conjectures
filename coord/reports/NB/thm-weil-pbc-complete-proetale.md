# Stage 1 report: thm-weil-pbc-complete-proetale

## Files written

- `dag/nodes/sec-proper-base-change/thm-weil-pbc-complete-proetale.json`: item split; no new nodes.
- `citations.json`: verbatim statement quotes for all step citations.

## Attachments

None. I searched both source trees for the blueprint tag and target declaration; no sorry-free declaration states this item.

## WANTED

None.

## Not duplicates

None: no new nodes were created.

## What I checked and changed

The item source is the blueprint file `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/thm-weil-pbc-complete-proetale.md`, whose proof has one paragraph. I opened the statements of each existing dependency in `dag/nodes/sec-proper-base-change/`: the finite-level theorem supplies each finite exchange isomorphism; the completed-map reduction identifies reductions with those maps; the completed-map definition supplies the ordered composite; the levelwise-cone lemma turns levelwise isomorphisms into an isomorphism; the direct-image-limits proposition supplies the derived-limit/direct-image comparison; and the coherence lemma supplies naturality, identity, and pasting. The imported step had omitted the last two citations from `uses` even though it mentioned the direct-image comparison and levelwise criterion in text. I rewrote the paragraph as four steps so every non-elementary inference is explicitly tied to the statement that provides it and made `proof_deps` the exact union of its uses.

I checked the hypotheses in the item against the blueprint: the adic datum, proper f, arbitrary g, derived I-completeness, compatible etale-origin witnesses for every K_n, and the specified completed exchange map are unchanged. The finite-level theorem is applied at each K_n with its witness; the reduction lemma supplies compatibility with transitions; the levelwise cone criterion applies to the tower morphism; and direct-image limits identify the composite with the stated target. No new mathematical statement was introduced. The zero object has the asserted zero exchange isomorphism.

Mathlib searches were run for the item using LeanFinder twice, Loogle twice, grep twice, and LeanSearch once; LeanSearch was unavailable. The hits were generic etale or categorical pullback declarations and do not state this pro-etale completed base-change theorem, so the item remains a project statement.

## Review by NB

I read the blueprint item and the seven cited DAG entries in full. Across steps 1–4, `thm-weil-pbc-finite-level-proetale` explicitly states that the pro-etale exchange map is an isomorphism, `lemma-weil-pbc-completed-map-reduction` explicitly states that reduction of the completed exchange is exactly the finite-level exchange, and `def-weil-pbc-completed-base-change-map` explicitly defines the ordered composite whose isomorphism is claimed. `lem-weil-pbc-levelwise-isomorphism-cones` states that a morphism whose every evaluation is an isomorphism is itself an isomorphism; `prop-weil-pbc-direct-image-limits` states the direct-image/derived-limit isomorphism used to identify the composite; and `lemma-weil-pbc-completed-exchange-coherence` states naturality, identity-square, and pasting properties. I verified each quote in `citations.json` is verbatim and long enough to identify the cited assertion.

I checked that the proof uses no hidden hypothesis beyond the item's adic coefficient datum, properness, arbitrary base-change morphism, derived completeness, and compatible witnesses. The zero-object and identity-square cases are consistent. There were no new nodes to test or search for duplicates. The final corrections are described below; the statement and hypotheses were preserved.

## Corrections after source review

I read Stacks proetale.tex, Tag 09C9 (theorem-proper-base-change), including its proof, and Tag 099N (lemma-pushforward-Noetherian-case). The source follows finite reduction, perfect projection formula and inverse-limit/direct-image commutation, matching the tower route. The adic datum expressly requires every quotient to be finite, verifying the finite-level theorem hypothesis. Upstream master Proper.lean at lines 104 and 114 has sorry declarations for condensed E and Qbar coefficients; these do not finish this integral adic item and those coefficient categories are not identified here.

On closer C4 review, the reduction lemma identifies reductions of the completed exchange, not tower evaluations. I repaired this: step 2 uses the actual middle arrow in the ordered composite and the levelwise criterion. Step 3 uses the ordered composite and direct-image-limits statement, explicitly cancels the inverses, and uses reduction only for the stated map identification. Step 4 uses coherence solely for the final blueprint sentence. Step 1 cites the adic datum for finiteness and the finite-level theorem for exchange isomorphisms. Every quote is now the full verbatim cited statement. No new nodes, no relocation of the item into a new lemma, and no use of a cited node's proof were needed. The zero object and identity square satisfy all the steps, including inverse cancellation.

## Second reading by NB

- Item statement: compared every hypothesis and the displayed completed exchange with the blueprint item and Stacks proetale.tex, Tag 09C9, label theorem-proper-base-change (lines 6187–6272): agrees with the blueprint; the blueprint adds finite perfect quotients and compatible chosen witnesses. The coefficient category is the adic sheaf category, not upstream master’s condensed field category.
- Step 1: read the adic datum and finite-level theorem statements; finiteness of every P_n and the bounded-below etale witness give exactly the required hypotheses. PASS. Checked n=1, K=0, finite-field coefficients with I=0, and the empty scheme; n=0 is outside the declared indexing n>=1.
- Step 2: read the completed-map definition, levelwise criterion, four-arrow definition and tower-compatibility statement; the original citations did not state the evaluation identification. FIX: four-arrows identifies v'_n with the finite exchange, and tower-compatibility explicitly recovers it by evaluation. Properness, the cartesian square and completeness hold in the four-corner construction. All four nodes are existing nodes in the same unit; no use of their proofs or relocation of the item.
- Step 3: read completed-map, direct-image-limits and completed-map-reduction in full against Stacks Tag 099N, label lemma-pushforward-Noetherian-case (lines 4336–4400), and Tag 09C9’s two limit formulas. PASS: direct-image-limits also supplies completeness of Rf_*K and compatible perfect projection-formula isomorphisms; the definition specifies both outer isomorphisms. Inverse cancellation proves the composite invertible. Reduction is used only for the supplementary identification, never as a tower evaluation.
- Step 4: read completed-exchange-coherence’s statement and the blueprint proof’s final sentence. PASS: naturality, identity, horizontal and vertical pasting are exactly its clauses; no such assertion is attributed to Stacks itself.
- New nodes: none; B1–B7, duplicate/special-case/Mathlib-leaf checks for new nodes are vacuous. Inspected the existing four-corner and four-arrow statements before reusing them. Zero-object and identity-square cases preserve all maps and cancellation.
- Source/attachment check: read upstream master Proper.lean’s two target declarations; they have different condensed E/Qbar coefficient categories and sorry bodies. The slopmaster2 ProEtale source search finds no target declaration or blueprint-id attachment. Neither is treated as a finished proof of this item.

Changes: repaired the remaining C3/C4 gap in step 2 by citing the existing four-arrow definition and tower-compatibility lemma; regenerated citations.json with the full verbatim statement per actual citation and recomputed proof_deps. No statement, first-worker report section, or new node was changed or added.
