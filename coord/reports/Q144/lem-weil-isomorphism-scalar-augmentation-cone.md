# Q144 stage-1 delivery: lem-weil-isomorphism-scalar-augmentation-cone

## Files written

- `dag/nodes/sec-six-functors/lem-weil-isomorphism-scalar-augmentation-cone.json`: statement, split into five proof steps; no Mathlib match for the full strict augmentation identity.
- `citations.json`: thirteen step/node quotations, checked against the verbatim live dependency statements.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed msearch command. `write_split.py` is sandbox-only preparation, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, created metadata and blueprint ancestry are retained. Searches made by Q99 and already recorded on the existing node are retained; Q144's logged searches are appended without pretending to have performed Q99's queries.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag and for scalar augmentation, quotient augmentation, inverse-image comparison, and Roos/completion terminology. The hits concern Tor-independent tensor augmentation, affine Koszul comparison and other different statements. No project declaration found states this full equality of specified chain maps with both cone coordinates. Generic Mathlib mapping-cone results are ingredients, not an attachment for this pro-etale comparison.

## WANTED

None.

## Findings and changes

The item was an unsplit statement with no proof. Its mathematical statement is correct with the explicitly fixed representatives and comparison maps. No STATEMENT-DISPUTED correction is needed. The proof has been supplied without introducing another node that merely restates its conclusion or a coordinate of it.

I read Bhatt–Scholze, *The pro-etale topology for schemes*, printed pp. 50–51, Lemma 6.5.9(4) and its proof: pullback followed by completion is the contextual operation. This lemma does not claim the coefficient-extension identity here and is not used as if it did. The proof is marked agent-written. I also read Stacks `sites-modules.tex`, Tag 03D6 (`definition-pushforward`, including its pullback clause), Section 03EK (`section-tensor-product`, sectionwise tensors, sheafification and associativity), and `derived.tex`, Tag 08TC (`definition-derived-limit`). The latter gives the Roos triangle, not uniqueness of a map into it. The proof instead uses the explicitly fixed two-coordinate cone from the comparison-definition node.

The current unit record is the migrated `sk-prop-sf-rf-shriek-preservation` record. This is an auxiliary node below the global-geometric-Frobenius definition, not that unit's key statement; no unit record is edited. I read the chapter and unit records and the main-20261015 global-Frobenius definition. The recorded blueprint place and via chain explain exactly which first transport-arrow coefficient compatibility this split supplies. Whole-blueprint searches for augmentation, scalar, quotient-cone and coefficient-change augmentations found no other blueprint statement of this strict identity; `blueprint.same_as` remains empty. DAG searches likewise found this item and its parent, together with related, genuinely different strict scalar-cone and trace-multiplication statements. No new node is proposed.

Mathlib searches used only the prescribed msearch command. Both semantic phrasings were read: the first returned generic mapping-cone constructions and the second returned module tensor/quotient and ordinary adic-completion naturality. Loogle first found no combined mappingCocone/ext hit, then located `CochainComplex.mappingCone.ext_to_iff`. I read `MappingCone.lean` around lines 170–185 and 435–452: these are degreewise two-projection extensionality and cochain constructors, not the particular coefficient compatibility. Grep found no Roos/completion augmentation theorem. A second grep found the generic cone/cocone constructors and extensionality. These results do not make the full item a one-line specialization: the two tensor calculations still have to be proved.

## What remains unfinished

Nothing required for this one-level stage-1 split. No Lean was written and no compiler, Lake or build tool was run. No repository or launcher file was written, and no git command was run by the worker. All worker writes are inside the assigned sandbox. Existing cited lemmas remain their owners' stage-1 obligations; they are used only through their statements.

## Review by Q144

I checked the delivery-errors B–E rules against the written item and opened every statement dependency, as well as every node used in the proof. Since there are no new nodes, there are no new-node self-containedness, missing searches, duplicate-tag pairs, statement-only-node, or new definition obligations. All five proof steps are under 800 characters; none hides a long comparison lemma. The proof-origin field accurately identifies this as an agent calculation rather than a quotation from Bhatt–Scholze. The statement is unchanged, and no clause is weakened.

For Step 1, the statement of `lem-weil-proetale-isomorphism-inverse-image` (1) gives precisely the sectionwise identification along the isomorphism of sites, not just full faithfulness. `def-weil-inverse-image-pullback-comparison` explicitly gives the completed coefficient ring isomorphism c_L. `def-pur-sheaf-tensor-product` explicitly defines the tensor as sheafification of the sectionwise tensor, so equality on pure tensor generators, followed by additivity and the universal property of sheafification, suffices. This step is marked non-elementary because it invokes the existing isomorphism-of-sites statement; it does not silently assume arbitrary inverse images are objectwise evaluation.

For Step 2 I used the actual augmentation in part (b) of `def-weil-inverse-image-pullback-comparison`, with its zero shifted coordinate, and the statement of `lem-weil-specified-pullback-comparison-alpha`, which explicitly sends BOTH cone coordinates by the product of d_m. A linear map sends zero to zero; no theorem about uniqueness from projections of a derived limit is used.

For Step 3 the same definition supplies the unshifted quotient augmentation, and the alpha node's stated d_m formula gives the output after setting both finite input coefficients to 1. I checked that its statement also explicitly identifies Q tensor B_L with P tensor B_L along rho_m and identifies the canonical tensor/product maps. This is direct substitution, not an appeal to the proof of alpha or an implicit assertion that all maps into a derived limit are determined by their reductions.

For Step 4 the statement of `lem-weil-isomorphism-scalar-tensor-kflat-model` gives exactly the local formula for b_P. The comparison definition supplies the Q augmentation and the equation pi_X c_L = c^g g^{-1}(pi_Y). The sheaf tensor definition supplies the ordinary balancing relations. First balancing inside Q tensor B_L changes (p tensor s_0) tensor 1 to p tensor pi_Y(s_0); balancing in the finite pullback moves that coefficient to c^g g^{-1}(pi_Y(s_0)). The displayed coefficient equation then makes this pi_X(s). Thus the equality is proved, not hidden behind the word 'transport'.

For Step 5 I checked both projections of the fixed direct-sum cone term, and every projection of the unshifted product. Product and direct-sum universal properties and degreewise equality of chain maps are elementary; the abstract-derived-category definition explicitly defines a chain map as a family of degree maps. The maps are already chain maps by the cited constructions; there is no extra homotopy or quasi-isomorphism being asserted. The sheaf tensor definition again justifies passage from sectionwise tensor generators to sheaves.

Hypotheses: g is an isomorphism throughout (needed for the site section formula and c_L); the two coefficient fields and rings, quotient maps and same-index iota_m are the ones in the alpha and model statements; m is at least 1; and P is the chosen flat-term K-flat model for K in D^b_c, so all three stated constructions apply. I did not apply Bhatt–Scholze's qcqs lemma to arbitrary schemes to prove this strict identity: it is background only. The calculation uses no finite-type, qcqs, normality, boundedness-of-P, or unramified-extension assumption. In particular, no identification of equal-index E and L quotients as rings is made.

I tested g = identity, E = L (including different unit choices of uniformizer), m = 1, a ramified extension with varpi_E = u varpi_L^e and e > 1, the zero complex, an empty scheme, and complexes with nonzero terms in multiple degrees. The same-index quotient map still exists in the ramified case, units still map to units, and the crucial coefficient on both sides is pi_L,m(s), never pi_E,m(s). Tensoring S_X placed in degree zero introduces no Koszul sign; both shifted coordinates remain literally zero. No correction to the statement was required.
