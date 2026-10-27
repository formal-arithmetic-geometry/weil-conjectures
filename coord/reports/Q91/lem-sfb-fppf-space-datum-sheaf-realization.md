# Stage-1 delivery: lem-sfb-fppf-space-datum-sheaf-realization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-space-datum-sheaf-realization.json`: statement, no Mathlib match; split into nine explicit steps, all under 1100 characters. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `searches.jsonl`: actual searches recorded by the authorized search command. `write_split.py` is a sandbox-only preparation script.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag, fppf datum, space datum, algebraic-space and descent terminology found no project declaration stating the item. The Hilbert functor's fppf sheaf documentation does not give this equivalence. No compiler was run.

## WANTED

None. All mathematical sources used are present.

## Findings and corrections

The item was unsplit, with an empty proof and with previous Mathlib search records. Its statement agrees with Stacks Tag 0ADT, equivalence and clause (1). The statement remains unchanged, including the absence of a global algebraicity conclusion. The source's final paragraph omits the quasi-inverse verification, and its coequalizer paragraph compresses the local-identification argument. The delivery writes these arguments explicitly rather than citing Tag 0ADT as its own proof dependency.

The pointwise coproduct of sections is used only as a presheaf: it is not identified with the sheaf coproduct. Its pointwise equivalence-relation quotient is sheafified using the existing plus theorem. There is no unsupported assertion that quotients or colimits are computed sectionwise in sheaves. All new searches are genuine logged queries. The existing historical searches are retained. The promising Mathlib `Pseudofunctor.isEquivalence_toDescentData` requires an `IsStack` hypothesis, as verified in `Mathlib/CategoryTheory/Sites/Descent/IsStack.lean`, lines 41–74. It cannot prove effectiveness for this slice construction without the result being established. Dense-subsite sheaf equivalences do not construct the descent realization either. The second semantic query and the Loogle and grep results were also read. No service failure has been recorded as a negative result.

The item has no machine-resolvable blueprint ancestor: `tools/blueprint_refs.py ancestor` reports `None`, consistent with its inherited null `from.node`. I retained that value and its detailed place/via chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, paragraph (3). The item is a sheaf-theoretic prerequisite below the inherited alteration/moduli route, not the unit's key node, so no unit record was changed. Whole-blueprint searches for `0ADT`, `descent sheaves`, `descent data`, `fppf`, `sheafification` and `equivalence relation` did not find an alternative blueprint statement of this item. DAG searches located the existing covering-calculus, plus and local-section nodes used here.

## Not duplicates

No new nodes. The existing sheafified-relation coequalizer lemma concerns an already specified sheafification of a relation between two sheaves; it is unnecessary for the direct quotient construction here. The finite locally free kernel-pair quotient lemma concerns schemes and a supplied finite locally free quotient morphism; those hypotheses do not hold here. Neither was duplicated or cited for a conclusion it lacks.

## Review by Q91

I read `spaces-descent.tex`, `lemma-descent-data-sheaves` (Tag 0ADT), including both directions, the displayed coequalizer, and the omitted verification. I read `spaces-topologies.tex`, `definition-fppf-covering` (03Y8), `lemma-fppf` (03Y9), the scheme-refinement lemma, and the sheaf-surjectivity lemma. For the sheafification inputs I read `sites.tex`, `theorem-plus` (00WB), `proposition-sheafification-adjoint` (00WH), and `lemma-sections-sheafification` (00WK). No SGA source is used. There are no new node sources to review.

Step 1 uses the actual algebraic-space definition (objects are fppf sheaves, arrows are natural transformations) and the fibre-product statement (the overlap products are algebraic spaces). Its explicit coordinate reordering verifies both the cocycle and functoriality. It does not require the general Yoneda lemma.

Step 2 uses the full statement of the existing covering-calculus node, especially clauses (1)–(4), and the atlas clause of the algebraic-space definition. The fibre-product node supplies algebraicity of each test pullback. The target of the pullback is a scheme T, and after choosing scheme atlases all sources are schemes, so the scheme-comparison clause genuinely applies. This is a short application of those clauses, not a claim that an arbitrary flat map of spaces is representable. No new local-lifting lemma was created for this elementary consequence.

Step 3 uses only the datum's hypotheses. Fixing all overlap coordinates makes the transports bijections on precisely the required fibres. The repeated-index cocycle proves identities, and the (i,j,i) cocycle proves inverses; these and the triple cocycle prove equivalence of the pointwise relation. The relation is preserved under restriction, so the quotient really is a presheaf. This is the relation used by the source's two coequalizer arrows.

Step 4 cites the plus theorem for existence of a sheafification, not just its definition. Its statement supplies both the actual double-plus construction and the universal map into a sheaf. The algebraic-space node says X is a sheaf, justifying that application. The size convention places the site, its arrows and I in a common larger universe; no small-index existence theorem is applied to an uncontrolled large diagram.

Step 5 uses exactly the local-equality sentence of the existing local-sections node. After the common base coordinate has been fixed, equality in the quotient says the two V_i sections differ by the identity transport. The algebraic-space definition and the site/sheaf definition justify detecting equality on a covering. Step 6 uses the local-representation sentence of the same node, with the pullback equality ensuring that tau_{j i} is defined. The injectivity already proved in step 5 makes the local preimages agree, so the sheaf axiom gives a global preimage and uniqueness. These are explicit injectivity and surjectivity arguments, without importing a mono/epi criterion.

Step 7 uses only the universal property of sheafification after explicitly checking the relation is preserved. The formula on sections proves that the reconstructed overlap maps are exactly the given ones, and compatibility of a family of datum morphisms gives its map of quotients. The same uniqueness proves the functor laws, so no unnamed descent-of-morphisms theorem is used.

Step 8 cites the sheafification universal property, the local-section representation theorem and the sheaf/covering axioms. The local lift of the base section is step 2, and equality of quotient representatives is exactly the canonical transition from step 1. Common refinements are obtained by the explicitly cited composition and base-change axioms. Local preimages glue because injectivity was proved first. The formulas on representatives prove naturality of the counit. Step 9 spells out the inverse map on Hom sets and uses step 2 plus sheaf separatedness for uniqueness; it also assembles the two natural isomorphisms already constructed.

I checked delivery-errors B–E against these files: self-contained unchanged statement; all proof dependencies exist; every cited statement was opened; every quotation is verbatim; no step uses a cited proof rather than its statement; no new node is an elementary fact, duplicate, or restatement of a clause. There is no newly introduced cycle because only existing generic site results and covering calculus are cited, none depending on the item. The two off-unit site results are declared as generic tool uses in `split_report.tool_uses`, with justification. No top-level `tool_uses` or reviewer field was written. All non-elementary steps are under 2000 characters; each is one local representation or universal-property argument, with all its operations explicit.

I tested the construction for the identity cover (the quotient recovers the given sheaf), multiple identical covering members (the relation identifies their copies via the supplied transports), an empty local V_i (all relevant fibres remain empty), empty covering members, and the empty covering of the empty X. Sheaves have exactly one section over an empty test by the empty-cover axiom, which is why sheafification rather than the raw pointwise quotient handles that case. No finiteness, representability of the a_i, or algebraicity of F is smuggled into the proof.

## Unfinished

None within the stage-1 item. Existing cited nodes remain in their live states; this delivery splits only its assigned item.
