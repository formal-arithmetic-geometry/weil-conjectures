# Q26 stage-1 delivery: lem-a1-space-monic-diagonal-tests

1. Files written: `dag/nodes/sec-purity-real-sheaves/lem-a1-space-monic-diagonal-tests.json` (statement, split; no exact Mathlib match), `citations.json`, and this report. `searches.jsonl` is the search command's own log. No new nodes, no Mathlib leaves, no Lean writes or compilation.
2. Attachments: none. The project declaration `CategoryTheory.Limits.isPullback_diagonal_map_of_mono` in `lean/WeilConjectures/Mathlib/CategoryTheory/Limits/Shapes/Diagonal.lean:77` concerns a monomorphism into X itself. Here only Y → X ×_T B is monic; its composite to X need not be monic. It does not state the whole item. Searching the blueprint tag and the notions in WeilConjectures found no exact project declaration.
3. WANTED: none.
4. The imported statement is correct. Its last sentence already explicitly fixes the compatible-pair convention, although the referenced algebraic-space definition does not itself spell out pointwise fibre products. We use that convention from the item's statement, not an extra theorem attributed to the definition. No statement or statement dependencies were changed. The two elementary inverse maps were previously unwritten.
5. Unfinished work: none for this one-level split. No new unsplit lemmas are needed.

## Sources and searches

Read GOAL.md, the stage-1 brief and stage document, worker role, SETUP's three levels, and delivery-errors B–E (including the repeated merged copy). Read the chapter and unit records for sec-purity-real-sheaves/sk-p-real-rankin and the current main-20261015 blueprint proof of lem-a1-affine-hc0. This is a geometric representability dependency below that blueprint node, not a replacement for the unit's Rankin–Selberg argument. There was no pre-existing sandbox split or report, and no repair record for this item was found.

For the item read Stacks spaces-morphisms.tex, Tag 03KL, label lemma-base-change-separated, whose proof identifies the base-changed diagonal; and Tag 03KQ, label lemma-composition-separated, whose proof factors the composite diagonal. Confirmed both tag/label associations in tags/tags. The explicit argument for the monomorphism into the base change is supplied here, so proof_origin is honestly `agent`. No SGA source is used.

Searched the whole DAG for those tags and for diagonal/monomorphism statements, and tools/blueprint_refs.py for diagonal, diagonal monomorphism, and monic diagonal. Related nodes include the parent permanence node, lem-trf-sheaf-pullback-diagonal, and scheme monomorphism-separated lemmas; none states this item independently. No new node was created. Read the complete statements of def-trf-algebraic-space, def-weil-closed-immersion, def-pc-fibre-product, lem-trf-space-fibre-products-etale-covers and lem-trf-sheaf-pullback-diagonal. In particular the latter's conditional statement is not used as an unconditional theorem about every sheaf.

Retained every inherited search and appended the five actual Q26 command results from searches.jsonl, with unchanged tool/query text. LeanFinder was tried with two distinct phrasings, plus Loogle, LeanSearch and grep. Read Mathlib/CategoryTheory/Limits/Shapes/Diagonal.lean:86–162 for pullbackDiagonalMapIso: it supplies a constituent comparison involving two arrows into a base change, not the entire monic-sheaf scheme-test assertion. The mono-diagonal instances alone do not identify our two tests or give the representability consequence. LeanSearch's closed equalizer result concerns schemes, not arbitrary algebraic spaces. Consequently the item remains a split statement rather than a Mathlib leaf.

## Review by Q26

I checked the actual Stacks proofs just named against the precise relative diagonals here. The common image beta is in h_B, and composing with b makes (x_1,x_2) a section of X ×_{h_T} X. At no point is X ×_S X substituted for that relative product. The argument follows the prescribed equality-locus route and does not invoke a separate separation theorem.

Step 1 uses def-trf-algebraic-space only for the meaning of h_D and the fact that morphisms are natural transformations. Evaluating d at 1_D and then using naturality writes out the representable-section correspondence directly. Expanding the compatible-pair convention gives the displayed descriptions of L(E) and R(E). This neither cites a fully faithful Yoneda statement for a stronger claim nor presupposes representability of these tests.

Step 2 uses no node: its only input is the item's injectivity hypothesis on j_E. Both sections have the SAME beta-component after every u:E → D. Equality of their X-components therefore gives equality in X_B(E), hence equality in Y(E). The converse follows by applying r_E. I checked that r itself need not be monic; the proof makes no such assumption.

Step 3 uses def-trf-algebraic-space solely to interpret the explicitly constructed natural transformations as morphisms. The inverse sends (u,x) to (u,y_1 restricted along u); step 2 proves this belongs to L(E). The two composite calculations are written out. For v:E' → E, both maps replace u by uv and restrict the same chosen y_1, so naturality is checked, not asserted by an unnamed base-change theorem. This calculation also proves compatibility with a replacement D' → D. The argument constructs actual inverses and hence requires no separate result saying an objectwise bijective map is an isomorphism.

Step 4 uses def-trf-algebraic-space for scheme-test representation and def-weil-closed-immersion for the property of Z → D already supplied by the hypothesis. The SAME scheme Z and SAME scheme morphism Z → D represent the other test by composing the isomorphisms over h_D. Thus no uncited preservation of closed immersions, Yoneda recovery of a new scheme map, or base-change theorem is needed. Identity j is injective and is allowed without a further hypothesis.

All step citations have verbatim statement excerpts in citations.json. No step takes information from a cited node's proof. All four steps are elementary expansions of the stated definitions and injectivity; together their text has 1946 characters, and none exceeds 2000. This keeps the real argument in the item instead of relabelling its clauses as new nodes. No proof dependency is off-unit except definition nodes, for which no tool-use declaration is needed.

For edge cases I tested j = identity, empty Y, empty D, equal y_1 and y_2, and distinct y_i that become equal only after a further test. The pointwise equivalence applies to each E and u, so no claim is made merely from equality on D or from equality of underlying points. Taking X = h_T and Y = h_B with j identity shows r need not be monic, but fixed beta still makes the argument valid. No finite-type, quasi-compactness, nonemptiness, or representability of j is silently assumed. There are no new statements to audit for small-case failures or duplicates, and no statement dispute was found.

## Not duplicates

No new nodes.
