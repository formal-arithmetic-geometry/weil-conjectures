# Stage-1 delivery: lem-sfb-closed-ideal-base-change-affine-diagram

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-ideal-base-change-affine-diagram.json`: item, eight proof steps, status split; Mathlib search found component results only.
- `citations.json`: 20 entries, one for every step/node citation, each quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's original log; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. A project-wide search for the exact blueprint id, closed-ideal base-change phrases and affine-diagram phrases found no declaration stating all clauses. `AlgebraicGeometry.closedSubscheme_baseChange_ideal_image` in `WeilConjectures/AlgebraicGeometry/ClosedSubschemeBaseChangeIdealImage.lean` states the existing ideal-image node, not the affine diagram item. I read its theorem and the separate canonical-structure-base-change theorem, neither of which gives the item. The conormal affine comparison concerns a further conormal pullback, not the present ideal sequence. I did not compile or write Lean.

## WANTED

None. All needed Stacks source files are present.

## Issues and changes

No statement dispute or source error was found, and the statement and statement dependencies are unchanged. The item was unsplit with no proof; the sandbox had no previous item or report. Its recorded searches were retained and six actual new search results appended. Both semantic phrasings returned ideal comap/spectrum components, not the entire canonical module diagram; Loogle's comap declaration and grep of Modules and IdealSheaf/Functorial likewise do not supply the unit-normalized section maps. Read Functorial.lean, including comap (line 39) and ker_fst_of_isClosedImmersion (line 80). This is not a Mathlib leaf by one-line specialization.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` reports null. I retained its detailed `from.place` and `via` chain and recorded the current latest blueprint clause in split_report. The current blueprint's unit is under sec-six-functors-basics rather than the older path in the unit record. I read the current `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3); this split remains the recorded algebraic prerequisite below that clause. The chapter and unit were not changed.

The exact ideal-image theorem is an off-unit generic tool and is declared in `split_report.tool_uses`. The other nontrivial ingredients already exist as Mathlib/closed or general algebraic-geometric nodes. No new nodes were necessary. Searches of the whole DAG by source tags and concepts and blueprint_refs searches for 'closed ideal', 'affine base change', 'base change of a closed', and 'pullback of a quasi-coherent' revealed no blueprint node equal to the entire statement. Related closed-immersion statements supply only some clauses; they are used rather than duplicated.

## Not duplicates

No new nodes. In particular, I reused `lem-pc-closed-subscheme-base-change-ideal-image`, `lem-weil-pbc-module-pullback-affine-sections`, `lem-weil-pbc-affine-pushforward-base-change`, and the existing open/affine fibre-product nodes. The balanced identity is a direct two-way tensor calculation in a proof step, not a new node.

## Review by NR

I read Stacks `schemes.tex` at Tag 01JU, label lemma-fibre-product-immersion, including its proof: it states an image ideal under arbitrary base change, not an injective pullback ideal. I also read Tag 01JR (lemma-open-fibre-product), Tag 01JQ (lemma-fibre-product-affines), Tag 01I9 (lemma-widetilde-pullback), and `coherent.tex` Tag 02KG (lemma-affine-base-change), including its final balanced tensor identity. The canonical-map normalizations are written as the agent's assembly from these sources and the existing nodes; the proof is marked agent, not falsely attributed verbatim to Stacks. There are no new node sources to check.

Step 1 uses the full fibre-product definition, not a definition pretending to prove base-change stability. Its test-scheme argument explicitly constructs inverse descriptions, preserving the projections. I opened the ideal-image node and verified that its statement defines exactly the composite with the adjoint structure-sheaf map used in this item. Applying it to i and h proves closedness and the image equality; no flatness is needed.

Step 2 takes quasi-coherence of the original ideal from its definition node, which explicitly includes that assertion. The pullback-quasi-coherent node says it for every scheme morphism. Structure modules are locally the associated free rank-one modules. The closed-immersion definition explicitly includes affineness. The affine pushforward node's first clause states preservation of quasi-coherence, so it applies to i' and the structure module. This step does not infer preservation from the definition of quasi-coherence alone.

Step 3 uses the affine pushforward node's algebra-isomorphism clause (2), not merely an abstract module isomorphism. Closed immersions satisfy its affine hypothesis. The structure-pullback node explicitly states that the adjoint of h-sharp is invertible, with its unit equation. Once these identifications are fixed, both quotient maps send 1 to 1 and are O-linear, so their equality follows on every open by s=s times 1. This verifies the canonical quotient compatibility, rather than assuming that an arbitrary isomorphism respects it.

Step 4 takes the actual quotient description on every affine open from the closed-immersion definition and the affine ideal identification from its ideal-sheaf node. The open-fibre-product node states exactly the intersection Q and compatibility with projections; the affine-spectra node states the tensor ring and both projection maps. Their application to Z gives the inverse-image chart, not merely a set-theoretic inverse image. The universal property determines the quotient tensor map.

Step 5 checks covering point by point: choose V first, then U and V' inside its two open inverse images. Schemes have affine neighbourhood bases, so no separatedness or quasi-separatedness is being assumed. We never require intersections of two unrelated affine opens to be affine.

Step 6 uses the affine-sections node with its actual hypotheses: I is quasi-coherent, U and Q are affine, and Q lies inside h^{-1}U. Its statement explicitly gives c(s tensor b)=b times eta(s), and naturality, exactly as quoted in citations.json. This avoids confusing a tilde pullback isomorphism with the specified pullback-unit normalization.

Step 7 writes out both balancing relations and both inverse composites on pure tensors. Thus there is no hidden reassociation lemma or new clause-restatement node. The A'-linearity follows from multiplying the A tensor R' factor, or transporting that action to J tensor R' through (x tensor r')(j tensor s')=xj tensor r's'. Step 8 uses only the affine-sections naturality and the structure-pullback unit equation, both explicitly present in the cited statements. The calculation gives a_Q(j tensor c)=(j tensor 1)c. The chart ring map from step 4 gives b_Q(x tensor r')=bar(x) tensor r'. Substituting the step-7 inverse gives the claimed sequence over R.

I checked delivery-errors B through E: all cited nodes exist; each statement was opened; sources have exact tags and labels; proof_deps is precisely the union of uses; all steps have elementary judgments, and the non-elementary applications are cited. No new statement-only node, duplicate, renamed item-clause, missing search, circular dependency, or unrecorded off-unit route is introduced. Every step is under 1000 characters, so none crosses the 2000-character hidden-lemma threshold. The statement uses ordinary Zariski modules throughout, not an etale or condensed coefficient category.

Edge cases checked: empty schemes/zero rings produce zero section modules; J=0 gives the zero ideal map; J=A gives the empty closed subscheme and the entire image ideal. With R=A=Z, J=(2), and R'=F_2, J tensor_Z F_2 is nonzero but its map to F_2 is zero, while B tensor_Z F_2=F_2 and b is the identity. This confirms that the proof asserts image equality and the displayed map, with no unjustified injectivity. Non-noetherian bases and non-finitely-generated ideals are allowed at every cited application.

## Unfinished work

None in this stage-1 split. Downstream existing nodes remain their own tasks. Mechanical server validation and direct delivery are performed after this report is written.
