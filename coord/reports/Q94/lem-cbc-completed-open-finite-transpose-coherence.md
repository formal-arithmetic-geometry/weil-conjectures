# Stage-1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-completed-open-finite-transpose-coherence.json`: item, statement, split. Mathlib verdict: no exact match; the generic Hom equivalence and derived-adjunction results do not specify the coefficient-reduction and open-unit comparisons required here.
- `citations.json`: one entry per step/node citation, quoting the cited statement verbatim. Full statements are retained so that normalization formulas and hypotheses are visible together.
- `searches.jsonl`: actual msearch output retained, including the two semantic phrasings, Loogle, grep, and LeanSearch. The inherited item searches are retained verbatim.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed because this is an auxiliary node, not the unit's statement.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact node id and by completed-open/finite-reduction/scalar-adjunction terminology. The extension-by-zero presheaf Hom formula, topological stalk-transition coherence and ordinary scalar adjunctions are not this assertion on completed-ring pro-etale derived strict towers. No declaration was claimed as an attachment; no compiler or Lake command was run.

## Wanted literature

None. The blueprint source, Stacks sources and all tool-node statements used here are available locally.

## Findings and changes

The item was unsplit, with an empty proof, and there was no prior item copy, report or search log in this sandbox. There is no repair note for this item. The statement has not changed. The coefficient flatness and quotient comparisons are used without invoking the completeness equivalence on an arbitrary input: only their explicitly universal finite-reduction clauses are needed.

The whole-DAG searches found the already available `lem-cbc-ringed-open-scalar-adjunction`, which supplies the actual presheaf-identity scalar comparison and both adjunction identities, including their strict-tower derived forms. Its stronger small-site statement avoids the unnecessary quasi-compactness hypothesis in the parent limit-coherence node. The generic flat common-quotient tower and ringed common-quotient pullback comparison supply the required strict and compositor normalizations. No new node is necessary, and no clause of the item was transferred into another task.

The source is the finite-exchange paragraph of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`. That paragraph does not itself prove the scalar transpose refinement: the explicit argument here is marked agent-written. Its final limit paragraph is outside this item's claim and is not used. In particular this split does not take arbitrary-open preservation of products from that paragraph. The unit and chapter route is retained: only the finite open factor of the completed exchange is treated.

## Not duplicates

No new nodes were created. Existing nodes were reused after reading their statements. The scalar-adjunction node gives the open scalar/unit/counit part but does not mention a cartesian square or the finite pullback comparisons a,d. The ringed common-quotient pullback node gives scalar insertion, quotient normalization and composite pullback coherence but does not state the open transpose identity. The flat common-quotient tower node gives a strict normalized reduction isomorphism, without the pulled-back open unit. These complementary tools leave the two required computations in the item's proof.

Blueprint searches used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `open unit`, `scalar`, `transpose` and `open-tensor`. The nearest ancestor is `thm-cbc-complete-proetale`; the current from.place was already specific and is retained. None of those blueprint nodes states this precise scalar finite-reduction strict transpose result, so same_as remains empty. Source/library searches are against the current read-only live clone; Mathlib searches used only msearch.py.

## Review by Q94

I read the chapter and unit records, the three-level route requirements, GOAL.md, the standing stage-1 brief, and both B--E blocks of delivery-errors.md. I checked the finite-exchange source paragraph against every part of the item and read the Stacks extension-by-zero construction (sites-modules.tex, Tags 03DI, 03CY and 03DJ), the K-flat derived pullback and tensor arguments (sites-cohomology.tex, Tags 06YY, 0G7E and 07A4), the constant-completion discussion (proetale.tex, Tag 099L), and the dual resolving-class criterion (derived.tex, Tag 06XN). The tags were checked against tags/tags, rather than inferred from changing section numbers. No SGA reference is used.

Step 1 cites `lem-cbc-ringed-open-scalar-adjunction`. I checked its statement, not its proof: it specifies exactly the identity on the extension-presheaf direct sums, and explicitly gives unit and counit equations after scalar restriction, exactness, termwise towers and unbounded derived descent. Its hypotheses are a small site, its slice at U', and a ring-sheaf map; the constant-to-completed map and the chosen site satisfy these. It requires neither coefficient flatness nor quasi-compactness. The counit equation in the step has c inserted in the correct direction, from r j'^* to G_j' r.

Step 2 uses `def-weil-pbc-adjunction-mate` only for the actual transpose formula. The remainder is written algebraically: naturality of e cancels e_C against b^{-1}, and counit naturality moves a inside J G. Domains are r J C -> N, equivalently J H -> N after b^{-1}; the final inside map has domain H and codomain G_j' N. This works for every derived x and makes no false claim that every derived arrow is an ordinary chain map. The cited definition gives the counit transpose, so C4 is satisfied.

Step 3 uses `lem-weil-pbc-diagram-kflat-replacements` to obtain P, and `lem-cbc-ringed-open-flat-resolution` to keep both K-flatness and flat terms after open extension. The latter explicitly includes strict tower replacements, not just a topological analogue. `lem-weil-pbc-constant-completion-equivalence` provides flatness of the completed ring over the constant ring and the quotient identifications for every n. `lem-weil-pbc-flat-common-quotient-reduction-tower` supplies a comparison on a single strict tower, with quotient units and transition maps. Its flatness and common-quotient hypotheses are exactly those just verified. `lem-sf-open-tensor-normalization` pins down the reduction/open tensor map and says that its restriction is the identity after the original open-unit identification, including diagram topoi. Thus reducing the unit is the actual p tensor t -> eta(p) tensor t map, not a chosen isomorphism.

Step 4 uses `lem-weil-pbc-ringed-common-quotient-pullback-comparison`. Its statement includes the scalar-insertion formula, inverse finite reductions, naturality in the input, and coherence for composable geometric morphisms. Both R -> B maps are flat by Step 3; J_n is I^n, and the finite coefficient maps identify the quotients on both sites. We do not assume u^{-1}A_T -> A_T' invertible. `lem-pur-cochain-pullback-tensor-coherence` gives the actual chain maps and equations for coefficient transitions and pullback composition, so this citation covers the reassociation and transition claims, not merely existence of a tensor isomorphism. The generator computation bar(s)t selects the same comparison as a,d.

Step 5 uses the identity normalization in `lem-sf-open-tensor-normalization` and the actual summands and unique sheafification factorization in `def-weil-extension-by-zero-presheaf` and `def-weil-presheaf-modules-sheafification`. The only pullback-compositor fact used here is already supplied by Step 4's common-quotient comparison. The generator from the original summand is taken to that same summand on either path; multiplying the final displayed equation by d^{-1} gives the asserted Psi identity with its stated orientation. I marked this step non-elementary because it uses the normalization tools; I did not hide it in a new node that restates the second clause.

Step 6 checks all b -> a quotient transitions, including a=b, using the explicit q_ba(t) formula and the coefficient chain equations in `lem-pur-cochain-pullback-tensor-coherence`. `lem-weil-pbc-diagram-kflat-replacements` applies to the small tower index and its product with a finite arrow category, so replacements are simultaneous and keep the original transitions. `lem-cbc-ringed-open-flat-resolution`, `lem-weil-pbc-flat-scalar-restriction-kflat`, and `lem-weil-pbc-ringed-pullback-preserves-kflat` state precisely the three resolving-class preservation assertions used. For scalar restriction the flatness hypothesis was verified in Step 3; ringed pullback does not require a flat coefficient structure map. This avoids treating a quotient tensor complex as K-flat, and avoids inferring equality in a derived tower category from equality of evaluations.

Step 7 cites `lem-pur-left-derived-from-kflat-class`: existence of replacements and quasi-isomorphism invariance were supplied in Steps 3 and 6, so its universal derived functor and counits apply. `lem-sp-exact-derived-transformation-pasting` says that the finite compositions and unit/counit equations of the exact functors descend to unbounded derived categories. I use it only for exact functors, never for arbitrary completed pullback. That is why the separate K-flat derivation is retained. Natural generator maps and universal comparisons give naturality in K; Step 2 gives naturality in x.

For B I checked that no incomplete new node, duplicate, invented Mathlib record, extra notion or wrong tag was added. For C I opened every cited statement and wrote one verbatim citation for every uses entry, and checked that none of these nodes has a dependency path back to this item. For D the two equations are proved in the item, rather than being re-labeled clauses; all non-elementary inputs are existing node statements. For E I checked the zero complex, empty open, identity open, zero finite quotient (I=A), equal indices and b >= a quotient composition. Identity opens reduce the formulas to ordinary naturality; empty opens give the unique map on zero towers. The formulas do not rely on nonzero quotients, injective transition maps, boundedness, completeness, or quasi-compactness. Every step is below 2000 characters; there is no long-step lemma hidden in the split. New statements tested: none.

Generic off-unit tools are declared in split_report.tool_uses with the hypotheses explained above. They supply coefficient algebra and localization while the unit's finite-open exchange route is unchanged. I made no changes to the repository, launcher scripts, Lean source, maintainer-owned metadata or another item.

## Unfinished work

None in the stage-1 split. The cited existing tasks retain their own project status. The maintainer independently reviews this direct delivery.
