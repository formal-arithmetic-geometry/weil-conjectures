# Stage-1 report: lem-coef-rigidification-postcomposition-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-rigidification-postcomposition-comparison.json`: repaired the retained five-step split; statement unchanged.
- `citations.json`: regenerated verbatim statement quotations for every citation in the revised steps.
- No new nodes; no Mathlib leaves. The root-level node copy is retained consistently but is not a delivery input.

## Attachments

None. Searches of both named read-only `WeilConjectures/` source trees for the item id, rigidification, coherent nerve and coherent realization found only unrelated Artin--Schreier/Picard rigidifications. No project declaration states this item. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, Sections 2.2.2 and 2.2.4, Theorem 2.2.5.1 and Appendix A.3.2, for this item. The online PDF https://www.math.ias.edu/~lurie/papers/HTT.pdf was read at printed pp. 88–89 (PDF pages 105–106) for the Q-resolution comparison and the Joyal/Bergner Quillen equivalence; it is not archived under `literature/`. No download was made. The proof is marked `proof_origin.by = agent`, as required for a reconstruction without a local archived source. The coherent Hom naturality input has its own Kerodon references 03N2/046J/03PD, and the canonical-composition input has Kerodon 01PF; those are existing node statements, not new unrepresented source citations.

## What was wrong or incomplete

The earlier five-step proof and report were retained as the starting point. Reading the current dependency statements exposed C4 in the earlier Step 2: `lem-coef-infinity-pinch-comparison` compares right mapping spaces with fixed-endpoint arrow spaces; it says nothing about coherent realization. It cannot justify the Map_S-to-D bridge. I replaced that inference with the already existing `lem-coef-pinched-rigidification-resolution`, using its two natural comparison squares explicitly. No helper node was created for an existing theorem or for a clause of this item.

Earlier Step 4 did not display why the comparison reflects weak equivalences back to raw D. The repaired step writes the strictly commutative enriched-functor square and checks its vertical weak equivalences. Earlier Step 5 asserted the edge-to-component bijection without identifying it; the repaired step uses the degree-zero clause of the Q-resolution and verifies composition after the faithful comparison to hW. The old report incorrectly called an unarchived reconstruction document-origin; this is corrected to agent-origin. HTT Proposition 3.2.2.10 is contextual to the item's original extraction (mapping simplices); it is not invoked as a standalone postcomposition theorem in the repaired proof.

## Searches and blueprint route

The inherited item searches remain, and all additional searches already logged by the prior attempt in `searches.jsonl` are now retained in `mathlib_searches` with their exact queries and outcomes. The two Loogle queries containing natural-language tokens returned unknown-identifier diagnostics; they are marked inconclusive, not negative searches. The later valid `"SimplicialNerve"` query returns the ordinary nerve, not the homotopy-coherent comparison. Two semantic phrasings and source grep find no exact Mathlib result. No search was invented or rerun to manufacture a log.

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, and the ancestor `prop-coef-integral-exceptional-adjoint.proof.md` in `literature/blueprint/main-20261015/`. The item is a technical prerequisite extracted beneath the ancestor's second paragraph, its derived mapping-complex adjunction. The existing from/via chain is preserved; this foundational split does not replace a geometric step of the unit. `tools/blueprint_refs.py search 'rigidification'` found only the two Picard nodes, and `search 'coherent nerve'` found none. The ancestor command confirms `prop-coef-integral-exceptional-adjoint`. No equivalent blueprint statement was found and `same_as` remains empty. This is not the unit's key statement, so no unit realization file is changed.

## Review by N7

I reopened the item, its unit/chapter and ancestor proof, and every cited node's current statement. I read the HTT comparison and Quillen-equivalence passages online, and used the precise existing DAG statements to reconstruct the additional deductions. No item hypothesis or conclusion has changed. There are no new-node sources to audit and no duplicate pairs requiring a Not duplicates section.

Step 1 uses the coherent-nerve comparison's object-preserving mapping-set replacement, Bergner fibration definition, and Quillen-equivalence clause; the Joyal model node supplies monomorphism cofibrations and categorical weak equivalences; rigidification equivalence detection supplies precisely that C[a] is Dwyer--Kan. I checked cofibrancy by the empty inclusion, fibrancy of RD by its Kan mapping sets and identity isomorphism lift, and essential surjectivity of r by its fixed objects. This replaces an unexplained derived-unit invocation with the defining adjoint-map criterion.

Step 2 uses only the pinched-rigidification-resolution statement, which actually states both theta and p as natural weak homotopy equivalences for the inputs at issue. I wrote both naturality equations. S and W are quasicategories by assumption and Step 1, respectively; C[a] is locally a weak equivalence by Step 1. The remaining inference is two-out-of-three on components and homotopy groups. I do not use the arrow-space pinch theorem to claim a realization comparison.

Step 3 uses exactly the Hom-bifunctor node's coherent natural transformation for a, with its action in the second variable by postcomposition, and the coherent-nerve node's vertex and enriched-composition clauses. The adjunction on Delta^1 sends its generating arrow to r([h]), so the edge on W is a(h), not an unrelated representative. Both equations have source M_S(w,y) and target M_W(aw,az), or the corresponding RD mapping set after inversion. Inversion is performed only in the homotopy category of spaces. These facts are stated by the cited nodes, including their higher compatibility; none is borrowed from a dependency's proof.

Step 4 uses the replacement theorem for the two actual maps r_wy and r_wz. Step 3 supplies the conjugacy of the Kan-valued horizontal maps. The definition node supplies the component-and-based-homotopy-group test for weak homotopy equivalences; the written strict square then reflects that property to the raw D composition map. I checked that this does not assume D is locally Kan and that the basepoint changes caused by homotopies are isomorphisms rather than equalities at different basepoints.

Step 5 uses the resolution's degree-zero statement to identify the hom-set bijection with h -> component([h]), the mapping-composition node for hS, edge representatives and its invertibility criterion, Hom functoriality for ha, and the coherent-nerve comparison for composition in hW and pi_0RD. Comparing through pi_0r and the coherent-nerve hom-set bijections forces F to respect identities/composition. Thus the cited nodes state all the claimed input, and the inverse functor on components is justified by bijectivity, not by a new choice of data from a sorry theorem.

For B–E I checked: no new statement-only node is secretly split; no new definition, duplicate, unsupported Stacks tag or SGA citation is introduced; every proof dependency occurs in uses and every uses has its verbatim quotation; the existing from/via metadata and imported statement are retained. The Q-resolution is strictly smaller independent input, not a restatement of the item's postcomposition clauses. Small cases checked are the empty quasicategory (pairwise assertions vacuous), a discrete category (empty off-diagonal spaces remain empty), the terminal category, identity h (both postcomposition classes are identities), and non-Kan raw mapping sets (the two vertical r maps are the only replacements used). All five steps are below 2000 characters; none hides a separate long comparison lemma. The earlier work's omissions, incorrect source-origin field, and invalid Loogle verdicts were repaired as described above.

## What could not be finished

No mathematical clause remains unproved at the natural-language split level. The missing archival HTT copy is recorded as WANTED; the required server dry run and delivery are handled by the delivery tool.
