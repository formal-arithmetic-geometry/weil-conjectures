# Stage-1 report: lem-sfb-space-lft-monomorphism-separated-lqf

## Files written
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-lft-monomorphism-separated-lqf.json`: item, statement, split; no Mathlib match for an arbitrary algebraic-space source.
- `citations.json`: all seven step/node citations, with verbatim statement quotations.
- `searches.jsonl`: five actual Mathlib searches recorded by msearch.py; all services answered.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments
None. Searched `lean/WeilConjectures/` for the exact blueprint tag, AlgebraicSpace, monomorphism/quasi-finite and Mono/Locally keywords. No project declaration states this algebraic-space result. Scheme monomorphism declarations do not cover its possibly nonschematic source. The Sheaf algebraic-space definition is reference material, not a finished proof of the item.

## WANTED
None.

## Findings and proof route
The imported statement is correct and unchanged. Its source is Stacks Tag 0463, `spaces-morphisms.tex`, lemma-monomorphism-loc-finite-type-loc-quasi-finite, lines 5361–5390. The source proves the scheme-chart conclusion by identifying self-products and analyzing fibres. The delivered proof uses the same monicity and representable etale charts, with an explicitly agent-written infinitesimal argument instead of the fibre computation: pull two competing lifts back to the etale scheme over the thickened test, use uniqueness there, then apply 02HE and 02V5. This is a node-level choice of foundational argument, not a departure from the unit's alteration/moduli route. No new lemma is concealed: the cancellation and pullback construction are written in step 2, and every theorem invoked is an existing node.

I read the chapter and unit records. The item is a subsidiary input, not the key unit statement, so no unit realization field is changed. `blueprint_refs.py ancestor` returns None for this pre-existing ancestry; the split preserves that null ancestor and the full place/via chain. Searching all blueprint nodes for monomorphism and the whole DAG for 0463, monomorphism/unramified/quasi-finite, and diagonal isomorphism found no duplicate of the item. Scheme-only lem-trf-monomorphism-finite-type-composite-lqf does not cover an algebraic-space source. The item itself is not made into a new node or clause node.

The unramified-to-locally-quasi-finite theorem `lem-weil-pbc-unramified-quasi-finite-at-points` is a generic tool filed in sk-thm-p1, declared in split_report.tool_uses: it supplies the exact scheme conclusion for each chart, and the unit has no local replacement. The two 02HE implication nodes are already Mathlib leaves. No SGA source is used.

## Mathlib search assessment
The five searches used the required msearch command: grep, leansearch, loogle, and two leanfinder phrasings. The exact queries and returned declaration lists are retained in the item and in searches.jsonl. I read Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:61: its monomorphism instance concerns schemes only. I also read QuasiFinite.lean:16–70: its locally quasi-finite class concerns schemes and does not itself require local finite type. These are useful components but not a match for this algebraic-space theorem. The inherited searches are retained verbatim.

## Review by Q61
I read Stacks 0463 in full and More on Morphisms 02HE (lemma-unramified-formally-unramified, lines 975–991), together with Morphisms 02V5 (lemma-unramified-quasi-finite, lines 7779–7787). There are no new nodes requiring separate sources.

Step 1 uses the exact closed-immersion definition in def-weil-closed-immersion. The sectionwise diagonal inverse commutes with restrictions; after any scheme base change it is an isomorphism onto the whole test scheme, so both the closed-image and structure-sheaf-surjectivity clauses hold. No theorem asserting separatedness of algebraic spaces was silently used.

Step 2 uses def-trf-algebraic-space for the meaning of a representable etale map: P = H' times_X V is a scheme and P to H' is etale. It uses def-weil-etale-morphism for etale implies unramified, and the actual statement of lem-weil-pbc-unramified-formally-unramified for uniqueness of the two sections across the first-order thickening. It uses def-weil-pbc-formally-unramified-morphism to identify the result with the required property of V to T. The two sections are over H', agree on H, and monicity is applied on H' itself, never just to geometric points. The map H' to X is an S-section because H' is over T over S. Thus every cited statement applies with its stated objects and hypotheses. The cancellation and pullback constructions are explicit; step 2 is marked non-elementary because it applies the cited uniqueness theorem. In that application the base is H′, the two composites with p are its identity, and the two restrictions along i agree.

Step 3 uses precisely the implication stated by lem-weil-pbc-lft-formally-unramified-unramified, with V and T both schemes, local finite type supplied by the hypothesis for this arbitrary chart and formal unramifiedness by step 2. Step 4 uses precisely the pointwise affine-neighbourhood conclusion of lem-weil-pbc-unramified-quasi-finite-at-points, matching pqf-def-quasifinite rather than silently substituting Mathlib's different ring-map convention. All cited node statements were opened and the quotations in citations.json are copied verbatim.

Small cases checked: empty X and empty charts (all conclusions vacuous or isomorphisms); identity X = h_T (ordinary etale charts are unramified); a closed immersion (no flatness assumption on f is used); nonsurjective monomorphisms; non-quasi-compact charts; and a nonseparated base S. No affine-product, finiteness, separated-base or quasi-compactness assumption is added. The generic point of a positive-dimensional integral scheme illustrates why local finite type cannot be dropped. No statement dispute was found. Each proof step is below 2000 characters; no long-step lemma extraction is needed. The assembly proof is below 3000 characters.

Against delivery-errors B–E: no new node, duplicate, hollow definition, clause restatement, source-only citation or cycle is introduced. Every non-elementary fact is an actual cited node; no cited proof is used in place of its statement. Sources use tags and labels, TeX is singly escaped in the decoded JSON, and no unperformed search is recorded. Nothing remains unfinished mathematically; the required remote dry run and push follow.

## Not duplicates
No new nodes; no new/existing same-tag pair to justify.

## Unfinished work
None beyond the required delivery checks at the time of writing this report.

## Repair of the returned delivery (2026-10-22)
The return at branch head `e5c73b12155` approved the mathematics but refused landing because the side completion had not been promoted to the live queue DAG. I retained its sandbox proof, report, citations and all inherited search entries. I compared the retained node with the current read clone: the statement, statement dependencies, source, creation record and blueprint ancestry agree; the current node is unsplit with no proof. The differences are the retained proof, proof dependencies, proof origin, split report, status and additional logged searches. There is no released repair note and no live finished proof superseding this work.

I reread all seven cited statements on the current DAG, rather than relying on their old proofs: the closed-immersion definition still covers isomorphisms; the algebraic-space definition still makes the pullback P a scheme with an etale projection; the etale definition supplies unramifiedness; the formal-unramifiedness theorem supplies uniqueness over the actual base H′; its definition supplies the affine test; 02HE applies to the locally finite type scheme map V to T; and 02V5 still supplies exactly the affine-neighbourhood local quasi-finiteness required by the item. Every retained quotation remains a verbatim substring, so none needs replacement. The changes to these nodes' proofs or review state do not alter any inference here.

I made the base and both equalities in the uniqueness application explicit and corrected step 2 from elementary to non-elementary. This avoids describing an invocation of the uniqueness theorem as merely definitional. The proof still uses no new node, preserves every clause of the statement and remains below the 3000-character assembly limit. I reread local Stacks 0463, 02HE and 02V5 and repeated the project-source attachment check; no declaration covers this algebraic-space theorem. The five searches in searches.jsonl have been read and reused without rerunning; earlier inherited Mathlib search records are preserved as history, not represented as searches performed during this repair.

The required initial dry run rebased the retained payload using deliver.py's temporary worktree and exited successfully at `11e370d59ec`. After the proof and report corrections I will run the final dry run and push through the same delivery tool. Promotion of the side completion is the maintainer's landing operation; this worker changes only the sandbox delivery.


## Latest returned head and live-DAG repair (2026-10-22)
The current return entry in coord/returns/Q61.md is the 13:36 UTC return of head `0f9f5acb9f3`, with the same side-completion promotion refusal. The earlier repair account above is retained as history. The latest initial dry run exited successfully at `0685a4209ca`; deliver.py rebuilt the retained payload on the current server DAG in its temporary worktree.

Against the current read clone, the retained item has identical statement, statement dependencies, source, chapter, unit, creation record and blueprint ancestry. The current live item remains unsplit, with no proof and no released repair note. The retained payload contributes its proof, proof dependencies, proof origin, split report, split status and five logged searches. I reused all five searches after reading their recorded results; no search has been invented or rerun.

I reread all seven current cited statements, including the current split of the unramified-to-quasi-finite node and the Mathlib status of the two 02HE implication nodes. Their statements still contain all seven exact citation quotations. No hypothesis change requires replacing a citation. The refreshed statement and file-hash evidence is in repair-current-citations.json; this is sandbox review material only.

For this retry I strengthened the actual proof text: step 1 now describes the pullback of the diagonal along an arbitrary pair of sections on W, constructs its unique section above each H-to-W, and identifies the resulting scheme projection with the identity of W. This proves both representability and closed immersion directly from the cited definition. Step 2 now explicitly writes q a = q b in h_T(H-prime) before invoking the sectionwise monomorphism, so the base of that cancellation is fully visible. The subsequent etale pullback, uniqueness over H-prime, and applications of 02HE and 02V5 retain their checked hypotheses. Thus this retry adjusts the mathematical payload as well as rebasing it.

I checked B–E again: the proof uses only existing nodes; its infinitesimal step is non-elementary and cites the uniqueness theorem; no scheme-only result is applied to X; both infinitesimal maps have the same structure map; the affine tests are square-zero thickenings; the output local-quasi-finiteness is the precise affine-neighbourhood notion in pqf-def-quasifinite. Empty sources, identity monomorphisms, closed immersions and non-quasi-compact charts require no extra hypotheses. No step exceeds 2000 characters, and the proof remains below 3000 characters in total. The statement and unit route are unchanged. The final dry run and push below are required before this retry is complete.


## Repair of head b09b6e0f219 (2026-10-23)
The latest return in coord/returns/Q61.md names head `b09b6e0f219` (2026-10-22 16:31 UTC). Its reader approved the proof, and landing refused the unpromoted side completion. I continued the retained sandbox, read its entire proof, report, citation file and actual search log, and ran the required initial dry run before editing. It exited 0 with `OK (not pushed)` at `2a0e52bbbb3`, rebasing through the delivery tool on the server's current DAG. No git command was run in the shared repository.

I compared every item field with the current read clone: statement, statement dependencies, source, chapter, unit, creation data and blueprint ancestry agree. The live item remains unsplit; the sandbox supplies the assembly proof and its metadata, plus the five preserved searches. There is no stage-1 repair-note file for the item. All seven cited files have the same SHA-256 hashes as the preceding repair inspection; nevertheless I reread every statement. `repair-current-citations.json` now records this return and comparison. All seven quotation checks passed against the current statement text. No inherited search was rerun or represented as newly performed.

The proof adjustment in this retry makes the last cancellation in step 2 explicit: the scheme pullback projection r to V has r s_a = a and r s_b = b; equality of the two sections therefore yields equality of the lifts. It also states that the square-zero thickening is over H-prime via i and the identity. Thus the uniqueness theorem is used with exactly its stated base and equal structure maps, rather than leaving that base change implicit. The retained statement and all dependencies remain faithful to Stacks 0463; the source of this alternative infinitesimal argument is still recorded as agent-written.

For the renewed B–E review I read Stacks 0463, 02HE and 02V5 in the local source. Step 1 uses only the closed-immersion definition and the explicitly constructed inverse of the diagonal. Step 2 uses the algebraic-space representable-etale definition to obtain a scheme P, the etale definition to obtain unramifiedness, the cited unramified-to-formally-unramified theorem for uniqueness on the given square-zero thickening, and its definition for the conclusion. Step 3 applies the converse 02HE node to V-to-T, with local finite type from the chart hypothesis and formal unramifiedness from step 2; no finite-presentation assumption is added. Step 4 applies the exact affine-neighbourhood conclusion of the 02V5 node. Every use remains supported by its quoted statement. All scheme morphisms have the specified bases, and the reasoning needs no quasi-compact chart, flat monomorphism, surjectivity of f or separated base. Empty charts, identity maps and closed immersions satisfy the argument without added conditions.

No new node, duplicate, circular dependence, clause restatement or unsupported theorem is introduced. The actual project-source tag and notion searches give no attachment for a potentially nonschematic algebraic-space source; the Mathlib declarations read still concern schemes. The altered proof has no step above 2000 characters and remains below the 3000-character assembly limit. The final remote dry run must pass before the subsequent push; promotion at landing remains the maintainer's operation.
